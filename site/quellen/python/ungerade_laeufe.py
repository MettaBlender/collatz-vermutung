"""Läufe ungerader Schritte (Lean: OddRuns.lean).

Sind x, T(x), …, T^(j-1)(x) alle ungerade, so teilt 2^j die Zahl x + 1, also j <= log2(x+1).
Scharf für Mersenne-Zahlen: T^j(2^j·a − 1) = 3^j·a − 1. In Z_2 dagegen hat −1 lauter
ungerade Schritte; für natürliche Zahlen ist das unmöglich.

    python ungerade_laeufe.py
"""

from __future__ import annotations


def T(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def laengster_lauf(n: int, schritte: int = 10 ** 5) -> tuple[int, int]:
    """(Länge des längsten Laufs ungerader Schritte, Startwert dieses Laufs) in der T-Folge."""
    best, start, lauf, x, kandidat = 0, n, 0, n, n
    for _ in range(schritte):
        if x == 1:
            break
        if x % 2:
            if lauf == 0:
                kandidat = x
            lauf += 1
            if lauf > best:
                best, start = lauf, kandidat
        else:
            lauf = 0
        x = T(x)
    return best, start


def main() -> None:
    print("Mersenne: T^j(2^j − 1) = 3^j − 1")
    for j in (1, 2, 5, 10, 20):
        x = 2 ** j - 1
        for _ in range(j):
            x = T(x)
        print(f"  j = {j:2d}: {x == 3 ** j - 1}")
    print("Längste Läufe ungerader Schritte (Länge <= log2(Start + 1)):")
    for n in (27, 255, 703, 77671, 2 ** 30 - 1):
        l, s = laengster_lauf(n)
        print(f"  n = {n:>10d}: Lauf der Länge {l:2d} ab {s}, 2^{l} <= {s} + 1: {2 ** l <= s + 1}")


if __name__ == "__main__":
    main()
