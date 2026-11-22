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
ungerade Schritte und 2510 Schritte insgesamt. Mit m > 2^68 (Computersuche aus der
Literatur) sind es über 186 Milliarden Schritte. Die Ungleichung oben ist hier nur in
Python nachgerechnet, nicht in Lean.

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


def main() -> None:
    print("log2(3) = [" + ", ".join(map(str, kettenbruch(LOG2_3, 15))) + ", ...]")
    print(f"{'Glieder >= m':>24} {'ungerade j':>14} {'gerade e':>16} {'Länge e+j':>18}")
    for name, m in (("2", 2), ("1 000", 1000), ("100 001 (Lean)", 100001), ("2^68 (Literatur)", 2**68)):
        j, e = min_zyklus(m)
        print(f"{name:>24} {j:>14,} {e:>16,} {e + j:>18,}".replace(",", "'"))


if __name__ == "__main__":
    main()
