"""Vier Kinder pro Knoten: Exponent 0.374 (Lean: FourKids.lean, Satz 46).

Ist c ein ungerader Vorfahre von n (3c + 1 = 2^E · n), so auch 64c + 21, denn
3(64c + 21) + 1 = 64(3c + 1). Jeder Knoten des Baums aus Satz 34 bekommt so vier Kinder
kid(n, b, h) < (6 oder 22) · (1 oder 64) · n. Wege der Länge t werden durch zwei Zahlen k, l < 2^t
codiert; mit a Nullbits in k und h Nullbits in l ist der Knoten <= 5 · 6^a · 22^(t-a) · 64^h.
Optimiert: etwa x^α Zahlen <= x erreichen die 1, (6^-α + 22^-α)(1 + 64^-α) = 1, α ≈ 0.374.

    python vier_kinder.py
"""

from __future__ import annotations

from math import comb, log

from crandall import child, erreicht
from gewichteter_baum import zeros


def kid(n: int, b: bool, h: bool) -> int:
    c = child(n, b)
    return 64 * c + 21 if h else c


def node4(t: int, k: int, l: int, wurzel: int = 5) -> int:
    if t == 0:
        return wurzel
    return kid(node4(t - 1, k // 2, l // 2, wurzel), k % 2 == 1, l % 2 == 0)


def alpha(eps: float = 1e-12) -> float:
    lo, hi = 0.0, 1.0
    while hi - lo > eps:
        mid = (lo + hi) / 2
        if (6 ** -mid + 22 ** -mid) * (1 + 64 ** -mid) > 1:
            lo = mid
        else:
            hi = mid
    return lo


def pruefe(t: int, wurzel: int = 5) -> bool:
    werte = {}
    for k in range(2 ** t):
        for l in range(2 ** t):
            v = node4(t, k, l, wurzel)
            a, h = zeros(t, k), zeros(t, l)
            if v > wurzel * 6 ** a * 22 ** (t - a) * 64 ** h or not erreicht(v, wurzel):
                return False
            werte[v] = (k, l)
    return len(werte) == 4 ** t


def main() -> None:
    for t in range(1, 6):
        print(f"t = {t}: 4^t = {4 ** t:5d} verschiedene Knoten, Schranke stimmt, alle erreichen 5: {pruefe(t)}")
    print(f"\nExponent α mit (6^-α + 22^-α)(1 + 64^-α) = 1: {alpha():.4f}"
          f" (Satz 45: 0.2912, Satz 34: {log(2) / log(22):.4f})")
    t = 80
    best = max(((a, h) for a in range(t + 1) for h in range(t + 1)),
               key=lambda p: log(comb(t, p[0]) * comb(t, p[1])) / log(5 * 6 ** p[0] * 22 ** (t - p[0]) * 64 ** p[1]))
    a, h = best
    x = 5 * 6 ** a * 22 ** (t - a) * 64 ** h
    n = comb(t, a) * comb(t, h)
    print(f"Beispiel t = {t}, a = {a}, h = {h}: {n:.3e} Zahlen <= {x:.3e}, also x^{log(n) / log(x):.3f}")


if __name__ == "__main__":
    main()
