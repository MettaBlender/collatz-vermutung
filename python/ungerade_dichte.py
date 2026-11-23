"""Ein Gegenbeispiel hat zu jeder Zeit mindestens 63.09 % ungerade Schritte (Lean: OrbitDensity).

Fällt m nie unter sich selbst, so gilt für jedes k: 2^k · m^o <= (3m+1)^o, mit o der Zahl der
ungeraden unter den ersten k Schritten von T. Mit m >= 2^27 folgt o/k >= log 2 / log(3 + 2^-27).
Dieses Skript berechnet die kleinsten erlaubten o und zeigt zum Vergleich, wie lange gewöhnliche
Zahlen über sich selbst bleiben und wie viele ungerade Schritte sie dabei machen.

    python ungerade_dichte.py
"""

from __future__ import annotations

import math

M = 2 ** 27


def T(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def min_ungerade(k: int, m: int = M) -> int:
    """Kleinstes o mit 2^k · m^o <= (3m+1)^o."""
    o = math.floor(k * math.log(2) / math.log(3 + 1 / m)) - 2
    while 2 ** k * m ** o > (3 * m + 1) ** o:
        o += 1
    return o


def ueber_sich(n: int) -> tuple[int, int]:
    """(Schritte, ungerade Schritte), solange T^i(n) >= n bleibt (bis zum ersten Abfall)."""
    x, k, o = n, 0, 0
    while True:
        if x % 2:
            o += 1
        x = T(x)
        k += 1
        if x < n:
            return k, o


def minimum_klassen_anteil(w: int) -> float:
    """Exakter Anteil der Klassen r < 2^(1000w) mit mindestens 630w ungeraden Schritten
    (Lean: MinClasses.lean, Schranke 2^(-49w)). Nach Terras binomialverteilt."""
    from fractions import Fraction
    k = 1000 * w
    gut = sum(math.comb(k, o) for o in range(630 * w, k + 1))
    return float(Fraction(gut, 2 ** k))


def main() -> None:
    print(f"Grenzwert log 2 / log 3 = {math.log(2) / math.log(3):.5f}")
    for k in (100, 1000, 10000, 100000):
        print(f"  k = {k:6d}: mindestens {min_ungerade(k):6d} ungerade Schritte")
    print()
    print("Zahlen, die lange über sich bleiben (Schritte bis zum Abfall, ungerade Schritte, Anteil):")
    for n in (27, 703, 10087, 35655, 270271, 362343, 381727, 626331, 1027431):
        k, o = ueber_sich(n)
        print(f"  n = {n:8d}: {k:4d} Schritte, {o:4d} ungerade, Anteil {o / k:.3f}")
    print()
    print("Mögliche Minima eines Gegenbeispiels: Anteil der Klassen modulo 2^(1000w)")
    for w in (1, 2, 3):
        print(f"  w = {w}: exakt {minimum_klassen_anteil(w):.3e}, Lean-Schranke 2^(-49w) = {2.0 ** (-49 * w):.3e}")


if __name__ == "__main__":
    main()
