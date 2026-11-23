import math

from collatz_core import (folge, gesamtstoppzeit, gesamtstoppzeiten, maximum,
                          sieb_check, sieb_ueberlebende, sieb_ueberlebende_bis, stoppzeit)
from stoppzeiten import rekorde
from verifizieren import pruefe
from zyklen import kettenbruch_naeherungen, zyklen_suchen


def test_bekannte_werte():
    assert gesamtstoppzeit(27) == 111
    assert maximum(27) == 9232
    assert stoppzeit(27) == 96
    assert folge(3) == [3, 10, 5, 16, 8, 4, 2, 1]


def test_gesamtstoppzeiten_mit_zwischenspeicher():
    t = gesamtstoppzeiten(2000)
    assert all(t[n] == gesamtstoppzeit(n) for n in range(1, 2001))


def test_sieb_wie_in_lean():
    # dieselben Zahlen beweist der Lean-Kernel in lean/Collatz/Sieve.lean
    assert sieb_ueberlebende(4) == [7, 11, 15]
    assert len(sieb_ueberlebende(8)) == 19
    assert len(sieb_ueberlebende(12)) == 226
    stufen = sieb_ueberlebende_bis(16)
    assert len(stufen[16]) == 2114
    assert sorted(stufen[12]) == sieb_ueberlebende(12)


def test_sieb_ist_korrekt():
    # jede Zahl in einer erledigten Restklasse fällt wirklich ab
    N = 256
    for r in range(N):
        if sieb_check(N, r):
            for a in range(50):
                n = N * a + r
                if n > 1:
                    assert stoppzeit(n) > 0


def test_stoppzeit_werte():
    # σ(n) = k + ceil(k·log2 3) für k ungerade Schritte (k ≥ 1), sonst 1
    erlaubt = {1} | {k + math.ceil(k * math.log2(3)) for k in range(1, 200)}
    assert {stoppzeit(n) for n in range(2, 20000)} <= erlaubt


def test_rekorde():
    t = gesamtstoppzeiten(100)
    assert [n for n, _ in rekorde(t)][:8] == [1, 2, 3, 6, 7, 9, 18, 25]


def test_verifikation():
    assert pruefe(1000)[0] == 250


def test_zyklen():
    assert list(zyklen_suchen(1, 1000)) == [(1, 4, 2)]
    neg = zyklen_suchen(-200, -1)
    assert (-1, -2) in neg and (-5, -14, -7, -20, -10) in neg
    assert len(neg) == 3


def test_kettenbruch():
    nb = kettenbruch_naeherungen(math.log2(3), 8)
    assert [(f.numerator, f.denominator) for f in nb][:6] == [(1, 1), (2, 1), (3, 2), (8, 5), (19, 12), (65, 41)]


def test_baum():
    from baum import ebenen, vorgaenger
    from collatz_core import gesamtstoppzeit
    assert vorgaenger(16) == [32, 5]
    assert vorgaenger(4) == [8]  # (4-1)/3 = 1 wird ausgeschlossen
    e = ebenen(20)
    for k, ebene in enumerate(e):
        assert all(gesamtstoppzeit(m) == k for m in ebene)


def test_terras_und_sieb():
    from paritaet import binomial_offen, ist_bijektion, paritaetsvektor, restklasse_von
    for k in range(1, 11):
        for r in range(2**k):
            assert restklasse_von(paritaetsvektor(r, k)) == r
    assert all(ist_bijektion(k) for k in range(1, 12))
    stufen = sieb_ueberlebende_bis(14)
    for k in range(1, 15):
        assert abs(len(stufen[k]) / 2**k - binomial_offen(k)) < 1e-12


def test_anstieg_2k_minus_1():
    """Wie Satz 9 (lean/Collatz/Climb.lean): 2^k·a − 1 → 3^k·a − 1 in 2k Schritten, nie darunter."""
    from collatz_core import schritt, sieb_check
    for k in range(1, 12):
        for a in (1, 2, 5):
            n = 2**k * a - 1
            x = n
            for _ in range(2 * k):
                x = schritt(x)
                assert x >= n
            assert x == 3**k * a - 1
        # Die Restklasse 2^k − 1 bleibt im Sieb offen.
        assert not sieb_check(2**k, 2**k - 1)


def test_varianten():
    from varianten import schicksal, zyklus_von
    assert zyklus_von(13, 5) == [13, 66, 33, 166, 83, 416, 208, 104, 52, 26]
    assert schicksal(13, 5) == ("zyklus", 13)
    assert schicksal(27, 3) == ("eins", 1)
    assert all(schicksal(n, 1)[0] == "eins" for n in range(1, 200))


def test_zyklen_laenge():
    import math
    from zyklen_laenge import min_zyklus

    def brute(m):
        c = math.log2(1 + 1 / (3 * m))
        j = 1
        while True:
            e = math.ceil(j * math.log2(3))
            if e - j * math.log2(3) <= j * c:
                return j, e
            j += 1

    for m in (2, 10, 1000, 100001):
        assert min_zyklus(m) == brute(m)
    assert min_zyklus(2**22) == (7621, 12079)
    assert min_zyklus(2**24) == (12276, 19457)  # Satz 18 in Lean
    assert min_zyklus(2**25) == (14271, 22619)  # Satz 25 in Lean
    assert min_zyklus(2**26) == (14936, 23673)  # Satz 26 in Lean
    assert min_zyklus(2**27) == (15601, 24727)  # Satz 27 in Lean


def test_zyklus_form():
    from decimal import Decimal
    from zyklen_laenge import LOG2_3, min_zyklus, zyklus_form

    assert zyklus_form(2**24) == ((665, 1054), (11611, 18403))  # Satz 19 in Lean
    assert zyklus_form(2**25) == ((665, 1054), (13606, 21565))  # Satz 25 in Lean
    assert zyklus_form(2**26) == ((665, 1054), (14271, 22619))  # Satz 26 in Lean
    assert zyklus_form(2**27) == ((665, 1054), (14936, 23673))  # Satz 27 in Lean
    for m in (2, 10, 1000, 2**22, 2**24):
        (j1, e1), (j2, e2) = zyklus_form(m)
        assert e2 * j1 - e1 * j2 == 1
        # das kleinste erlaubte (j, e) ist die Summe der beiden Nachbarn
        assert min_zyklus(m) == (j1 + j2, e1 + e2)
    # alle erlaubten (j, e) mit kleinem j haben die Form a·(j1, e1) + b·(j2, e2)
    m = 10
    (j1, e1), (j2, e2) = zyklus_form(m)
    oben = (Decimal(3) + Decimal(1) / m).ln() / Decimal(2).ln()
    for j in range(1, 400):
        for e in range(1, 2 * j + 1):
            if LOG2_3 < Decimal(e) / j <= oben:
                a, b = e2 * j - j2 * e, e * j1 - e1 * j
                assert a >= 1 and b >= 1 and a * j1 + b * j2 == j and a * e1 + b * e2 == e
    assert sum(min_zyklus(2**68)) == 186265759595


def test_zyklus_gleichung():
    from zyklus_gleichung import zyklen_aus_vektoren
    alle3 = set().union(*zyklen_aus_vektoren(16).values())
    assert alle3 == {1, 2}
    alle5 = set().union(*zyklen_aus_vektoren(10, q=5).values())
    assert {13, 17, 1} <= alle5


def test_ausnahmen_dichte():
    from paritaet import ausnahmen, paritaetsvektor
    for k in range(1, 13):
        direkt = sum(1 for r in range(2**k) if 2 * 3 ** sum(paritaetsvektor(r, k)) > 2**k)
        assert ausnahmen(k) == direkt
    assert ausnahmen(8) == 93  # wie das Lean-Beispiel
    assert ausnahmen(160) / 2**160 < 0.001


def test_einszyklen():
    from einszyklen import kritische_o
    assert kritische_o(3000) == []
    assert 1 in kritische_o(5, schranke=1)  # ohne die Schranke 2^22 geht es (trivialer Zyklus)


def test_binomialverteilung():
    """Satz 20 (Lean: count_odds): genau C(k, j) Klassen mod 2^k haben j ungerade Schritte."""
    from collections import Counter
    from math import comb

    def ungerade(n, k):
        o = 0
        for _ in range(k):
            if n % 2:
                o += 1
                n = (3 * n + 1) // 2
            else:
                n //= 2
        return o

    for k in range(1, 13):
        zaehler = Counter(ungerade(r, k) for r in range(2**k))
        assert all(zaehler[j] == comb(k, j) for j in range(k + 1))


def test_koeffizienten_stoppzeit():
    from koeffizienten_stoppzeit import pruefe, stoppzeiten

    assert stoppzeiten(3) == (4, 4)
    assert stoppzeiten(27) == (59, 59)
    assert pruefe(20000)[0] == 0


def test_vielfache_drei():
    from vielfache_drei import drei_phase, pruefe
    assert drei_phase(96) == 6  # 96, 48, 24, 12, 6, 3, dann 10
    assert drei_phase(7) == 0
    assert pruefe(20_000) == 13  # 3·2^12 = 12288


def test_negative_zyklen():
    from varianten import negative_zyklen
    z = negative_zyklen(5000)
    assert [len(c) for c in z] == [2, 5, 18]
    assert z[1] == [-5, -14, -7, -20, -10]
    assert z[2][0] == -17


def test_paritaetszyklen():
    from paritaetszyklen import startpunkt, zyklen
    assert startpunkt(0b01, 2) == 1  # 1 → 2 → 1
    for p in range(1, 13):
        assert zyklen(p) == ({1, 2} if p % 2 == 0 else set())


def test_sprungstellen():
    from zyklen_laenge import sprungstellen

    sp = dict(sprungstellen(25, 33))
    assert 28 not in sp and 30 not in sp  # 2^28 und 2^30 bringen nichts Neues
    assert sp[27] == 40328 and sp[29] == 122703 and sp[31] == 205078


def test_potenz_abfall():
    from math import comb

    from potenz_abfall import ausnahme_anteil, faellt_ab, lean_schranke, verteilung
    assert verteilung(10) == [comb(10, o) for o in range(11)]
    for w in (1, 2, 5, 20):
        assert ausnahme_anteil(w) <= lean_schranke(w)
    assert ausnahme_anteil(20) < ausnahme_anteil(10) < ausnahme_anteil(1)
    assert all(faellt_ab(n) for n in range(2 ** 32, 2 ** 32 + 50))
    from potenz_abfall import korec_anteil, korec_schranke
    assert korec_anteil(1) <= korec_schranke(1) < 1
    assert korec_anteil(3) <= korec_schranke(3)


def test_zweiadisch():
    from zweiadisch import aus_paritaeten, endet_in_eins_null, erreicht, paritaeten, vorfahren
    for n in (1, 5, 7, 22, 1000):
        for m in vorfahren(n, 4):
            assert m % 2 == 1 and erreicht(m, n)
    for n in (0, 1, 27, 12345):
        assert aus_paritaeten(paritaeten(n, 20)) == n % 2 ** 20
    assert aus_paritaeten([1] * 12) == 2 ** 12 - 1
    assert all(endet_in_eins_null(n) for n in range(1, 500))


def test_ungerade_dichte():
    from ungerade_dichte import M, min_ungerade, ueber_sich
    assert min_ungerade(1000) == 631 and min_ungerade(10000) == 6310
    # Lean-Schranke 2^j n^o <= (3n+1)^o für jedes Anfangsstück, solange die Folge über n bleibt
    from ungerade_dichte import T
    for n in (27, 703, 10087, 35655):
        k, _ = ueber_sich(n)
        x, o = n, 0
        for j in range(k):
            assert x >= n and 2 ** j * n ** o <= (3 * n + 1) ** o
            o += x % 2
            x = T(x)
    assert M == 2 ** 27


def test_crandall():
    from crandall import child, ebene, erreicht_eins
    assert (child(5, False), child(5, True)) == (13, 53)
    for t in range(9):
        e = ebene(t)
        assert len(set(e)) == 2 ** t and max(e) <= 5 * 22 ** t
        assert all(n % 2 == 1 and n % 3 != 0 and erreicht_eins(n) for n in e)


def test_masstreue():
    from masstreue import tabelle, urbilder
    for j, k in [(1, 3), (2, 4), (4, 4), (6, 3)]:
        t = tabelle(j, k)
        assert len(t) == 2 ** (j + k) and set(t.values()) == {1}
    for s in range(32):
        u = urbilder(s, 5)
        assert len(u) == 2 and 2 * s in u


def test_vorfahren_klassen():
    from vorfahren_klassen import erreicht, ist_primitivwurzel, vorfahre
    assert all(ist_primitivwurzel(j) for j in range(1, 7))
    for n in (1, 5, 7, 11):
        for s in range(64):
            m = vorfahre(n, 6, s)
            assert m % 64 == s and erreicht(m, n)


def test_minimum_klassen():
    from ungerade_dichte import minimum_klassen_anteil
    for w in (1, 2):
        assert minimum_klassen_anteil(w) <= 2.0 ** (-49 * w)
