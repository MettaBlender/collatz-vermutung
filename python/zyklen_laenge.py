"""Wie lang müsste ein nichttrivialer Zyklus mindestens sein?

Angenommen, ein Zyklus hat j ungerade und e gerade Glieder, und alle Glieder sind >= m.
Multipliziert man die Faktoren aller Schritte (3 + 1/n für ungerade n, 1/2 für gerade),
kommt man wieder beim Start an:

    3^j · Π (1 + 1/(3n))  =  2^e      (Produkt über die ungeraden Glieder n)

Jeder Faktor 1 + 1/(3n) liegt zwischen 1 und 1 + 1/(3m), also

    0  <  e − j·log2(3)  <=  j · log2(1 + 1/(3m)).

e/j muss also sehr knapp über log2(3) liegen. Die kleinste solche Zahl j findet man
unter den Näherungsbrüchen (Kettenbruch) von log2(3). Daraus folgt eine Mindestlänge
e + j für jeden nichttrivialen Zyklus.

Mit m > 100 000 (in Lean bewiesen, siehe Cycles.lean) ergibt sich: mindestens 971
ungerade Schritte und 2510 Schritte insgesamt, mit m >= 2^22 (VerifiedHugeAll.lean)
mindestens 7621 ungerade und 19 700 Schritte insgesamt. Mit m > 2^68 (Computersuche aus
der Literatur) sind es über 186 Milliarden Schritte. Die Fälle 100 001 und 2^22 sind auch
in Lean bewiesen (CycleLength.lean, VerifiedHugeAll.lean), der Fall 2^68 nur hier in Python.

Genauer (Eliahou-Typ, `zyklus_form`): Mit m >= 2^24 hat jeder weitere Zyklus
665a + 11611b ungerade Glieder und die Länge 1719a + 30014b mit a, b >= 1
(in Lean bewiesen, CycleShape.lean).

    python zyklen_laenge.py
"""

from __future__ import annotations

from decimal import Decimal, getcontext

getcontext().prec = 120
LOG2_3 = Decimal(3).ln() / Decimal(2).ln()


def kettenbruch(x: Decimal, n: int) -> list[int]:
    a = []
    for _ in range(n):
        q = int(x)
        a.append(q)
        x = 1 / (x - q)
    return a


def obere_naeherungen(n_glieder: int = 60) -> list[tuple[int, int]]:
    """Alle Haupt- und Nebennäherungsbrüche e/j von log2(3) mit e/j > log2(3), nach j sortiert.

    Der Bruch mit dem kleinsten Nenner in einem Intervall (log2 3, log2 3 + c] ist immer
    einer davon (Stern-Brocot-Baum).
    """
    a = kettenbruch(LOG2_3, n_glieder)
    p0, q0, p1, q1 = 1, 0, a[0], 1
    res = []
    for ai in a[1:]:
        for t in range(1, ai + 1):
            res.append((t * p1 + p0, t * q1 + q0))
        p0, q0, p1, q1 = p1, q1, ai * p1 + p0, ai * q1 + q0
    return sorted(((e, j) for e, j in res if Decimal(e) / j > LOG2_3), key=lambda t: t[1])


def min_zyklus(m: int) -> tuple[int, int]:
    """Kleinstes (j, e), das die Ungleichung für Glieder >= m erlaubt."""
    c = (1 + Decimal(1) / (3 * m)).ln() / Decimal(2).ln()
    for e, j in obere_naeherungen():
        if e - j * LOG2_3 <= j * c:
            return j, e
    raise ValueError("mehr Kettenbruchglieder nötig")


def zyklus_form(m: int) -> tuple[tuple[int, int], tuple[int, int]]:
    """Nachbarn (j1, e1), (j2, e2) im Stern-Brocot-Baum mit e1/j1 < log2(3) und
    e2/j2 >= log2(3 + 1/m), zwischen denen kein weiterer Knoten das Intervall trennt.

    Wegen e2·j1 − e1·j2 = 1 ist jedes (j, e) eines Zyklus mit Gliedern >= m eine Summe
    a·(j1, e1) + b·(j2, e2) mit a, b >= 1 (in Lean für m = 2^24: CycleShape.lean).
    """
    oben = (Decimal(3) + Decimal(1) / m).ln() / Decimal(2).ln()
    e1, j1, e2, j2 = 1, 1, 2, 1
    while True:
        e, j = e1 + e2, j1 + j2
        x = Decimal(e) / j
        if x <= LOG2_3:
            e1, j1 = e, j
        elif x >= oben:
            e2, j2 = e, j
        else:
            return (j1, e1), (j2, e2)


def sprungstellen(k_von: int, k_bis: int) -> list[tuple[int, int]]:
    """Die Exponenten k in [k_von, k_bis], bei denen die Mindestlänge eines weiteren
    Zyklus für Glieder >= 2^k grösser wird als bei 2^(k-1), mit der neuen Länge."""
    out = []
    vorher = sum(min_zyklus(2 ** (k_von - 1)))
    for k in range(k_von, k_bis + 1):
        laenge = sum(min_zyklus(2 ** k))
        if laenge > vorher:
            out.append((k, laenge))
        vorher = laenge
    return out


def main() -> None:
    print("log2(3) = [" + ", ".join(map(str, kettenbruch(LOG2_3, 15))) + ", ...]")
    print(f"{'Glieder >= m':>24} {'ungerade j':>14} {'gerade e':>16} {'Länge e+j':>18}")
    for name, m in (("2", 2), ("1 000", 1000), ("100 001 (Lean)", 100001), ("2^22 (Lean)", 2**22), ("2^24", 2**24), ("2^25 (Lean)", 2**25), ("2^26 (Lean)", 2**26), ("2^27 (Lean)", 2**27), ("2^68 (Literatur)", 2**68)):
        j, e = min_zyklus(m)
        print(f"{name:>24} {j:>14,} {e:>16,} {e + j:>18,}".replace(",", "'"))
    print("\nSprungstellen 2^k (ab hier wächst die Schranke):")
    for k, laenge in sprungstellen(20, 40):
        print(f"  2^{k}: mindestens {laenge:,} Schritte".replace(",", "'"))
    print("\nForm der Länge (a, b >= 1):")
    for name, m in (("2^22", 2**22), ("2^24", 2**24), ("2^25 (Lean)", 2**25), ("2^26 (Lean)", 2**26), ("2^27 (Lean)", 2**27), ("2^68", 2**68)):
        (j1, e1), (j2, e2) = zyklus_form(m)
        print(f"{name:>12}: j = {j1}a + {j2}b, Länge = {j1 + e1}a + {j2 + e2}b")


if __name__ == "__main__":
    main()
