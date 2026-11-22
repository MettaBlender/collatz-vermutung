"""Alle Zyklen einer festen Länge über ihre Paritätsvektoren finden (Satz 24).

Für T(n) = n/2 bzw. (3n+1)/2 gilt 2^p · T^p(n) = 3^o · n + c, und c hängt nur vom
Paritätsvektor v ab:  c = Σ_{i : v_i = 1} 3^(Einsen nach i) · 2^i.
Ein Zyklus mit Vektor v hat also den Startpunkt n = c / (2^p − 3^o) (Böhm–Sontacchi,
in Lean: `Collatz.cycle_unique_of_parVec`). Wir probieren alle 2^p Vektoren durch und
behalten die, bei denen n eine positive ganze Zahl ist, deren Paritäten wirklich v sind.
"""

from __future__ import annotations

import argparse


def T(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def paritaeten(n: int, p: int) -> int:
    """Paritätsvektor der Länge p als Bitmaske (Bit i = Parität von T^i(n))."""
    v = 0
    for i in range(p):
        if n % 2:
            v |= 1 << i
        n = T(n)
    return v


def startpunkt(v: int, p: int) -> int | None:
    """Der einzige mögliche Zyklus-Startpunkt zum Vektor v, oder None."""
    o = bin(v).count("1")
    nenner = 2**p - 3**o
    if nenner <= 0:
        return None
    c, einsen_danach = 0, 0
    for i in reversed(range(p)):
        if v >> i & 1:
            c += 3**einsen_danach * 2**i
            einsen_danach += 1
    if c % nenner:
        return None
    n = c // nenner
    if n <= 0 or paritaeten(n, p) != v:
        return None
    return n


def zyklen(p: int) -> set[int]:
    """Alle Startpunkte n ≥ 1 mit T^p(n) = n."""
    erg = set()
    for v in range(1 << p):
        n = startpunkt(v, p)
        if n is not None:
            m = n
            for _ in range(p):
                m = T(m)
            assert m == n
            erg.add(n)
    return erg


def main(argv: list[str] | None = None) -> None:
    a = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    a.add_argument("--bis", type=int, default=18, help="grösste Periode p")
    args = a.parse_args(argv)
    for p in range(1, args.bis + 1):
        z = zyklen(p)
        print(f"p = {p:2d}: {2**p:7d} Vektoren, periodische Startpunkte: {sorted(z)}")


if __name__ == "__main__":
    main()
