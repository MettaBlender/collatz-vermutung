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
    from paritaet import binomial_offen, ist_bijektion
    assert all(ist_bijektion(k) for k in range(1, 12))
    stufen = sieb_ueberlebende_bis(14)
    for k in range(1, 15):
        assert abs(len(stufen[k]) / 2**k - binomial_offen(k)) < 1e-12
