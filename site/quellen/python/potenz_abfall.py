"""Potenz-Abfall: fast alle n fallen unter 2·n^(31/32) (Lean: PowerDrop.lean).

Für n im Bereich 2^(32w) <= n < 2^(32w+1) betrachten wir die Klasse r = n - 2^(32w) und die
Zahl o der ungeraden Schritte unter den ersten 32w Schritten von T. Ist
2^(w+1)·3^o <= 2^(32w), so fällt die Folge von n beweisbar unter n / 2^w, also unter
2^(1/32)·n^(31/32).

Nach dem Satz von Terras ist o über die 2^k Klassen binomialverteilt: genau C(k, o) Klassen
haben o ungerade Schritte. Damit lässt sich der Anteil der Ausnahmen exakt berechnen, auch für
k = 32w mit riesigem 2^k. Lean beweist die Schranke Anteil <= (3^32 / 2^51)^w ≈ 0.823^w.

    python potenz_abfall.py
"""

from __future__ import annotations

from fractions import Fraction
from math import comb


def T(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def ungerade_schritte(k: int, n: int) -> int:
    """Zahl der ungeraden Werte unter n, T(n), …, T^(k-1)(n)."""
    o = 0
    for _ in range(k):
        if n % 2:
            o += 1
        n = T(n)
    return o


def verteilung(k: int) -> list[int]:
    """Wie viele Klassen r < 2^k haben o ungerade Schritte (o = 0..k)? Nachgezählt."""
    v = [0] * (k + 1)
    for r in range(2 ** k):
        v[ungerade_schritte(k, r)] += 1
    return v


def ausnahme_anteil(w: int) -> Fraction:
    """Exakter Anteil der Ausnahmeklassen modulo 2^(32w) (mit der Binomialverteilung)."""
    k = 32 * w
    schlecht = sum(comb(k, o) for o in range(k + 1) if 2 ** k < 2 ** (w + 1) * 3 ** o)
    return Fraction(schlecht, 2 ** k)


def lean_schranke(w: int) -> Fraction:
    """Die in Lean bewiesene Schranke (3^32 / 2^51)^w."""
    return Fraction(3 ** 32, 2 ** 51) ** w


def faellt_ab(n: int, schritte: int = 100000) -> bool:
    """Erreicht die Collatz-Folge von n einen Wert x mit x^32 < 2·n^31?"""
    ziel = 2 * n ** 31
    x = n
    for _ in range(schritte):
        if x ** 32 < ziel:
            return True
        x = x // 2 if x % 2 == 0 else 3 * x + 1
    return False


def main() -> None:
    print("Verteilung der ungeraden Schritte für k = 12 (nachgezählt = Binomialkoeffizienten):")
    v = verteilung(12)
    print("  ", v)
    print("   Binomial:", [comb(12, o) for o in range(13)])
    print()
    print(" w   k=32w   Ausnahme-Anteil (exakt)   Lean-Schranke 0.823^w")
    for w in (1, 2, 3, 5, 10, 20, 40, 80):
        a = ausnahme_anteil(w)
        print(f"{w:2d} {32 * w:6d}   {float(a):22.3e}   {float(lean_schranke(w)):18.3e}")
    print()
    import random
    random.seed(1)
    stichprobe = [random.randrange(2 ** 32, 2 ** 33) for _ in range(2000)]
    gut = sum(faellt_ab(n) for n in stichprobe)
    print(f"Stichprobe: {gut} von 2000 Zahlen in [2^32, 2^33) fallen unter 2·n^(31/32).")


if __name__ == "__main__":
    main()
