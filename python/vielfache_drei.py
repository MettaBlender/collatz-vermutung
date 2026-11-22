"""Vielfache von 3 in Collatz-Folgen (Satz 22).

Ein Schritt macht aus einer Zahl, die nicht durch 3 teilbar ist, nie ein Vielfaches
von 3. Vielfache von 3 kommen darum nur ganz am Anfang einer Folge vor, solange
halbiert wird. In Lean bewiesen: kein Zyklus enthält ein Vielfaches von 3
(`Collatz.periodic_not_mul_three` in `lean/Collatz/ModThree.lean`).
"""

from __future__ import annotations

import argparse

from collatz_core import folge


def drei_phase(n: int) -> int:
    """Wie viele Glieder am Anfang der Folge von n durch 3 teilbar sind."""
    k = 0
    for x in folge(n):
        if x % 3:
            break
        k += 1
    return k


def pruefe(grenze: int) -> int:
    """Prüft für 1 ≤ n < grenze, dass Vielfache von 3 nur im Anfangsstück vorkommen
    und dort nur halbiert wird (n = 2^k · x). Gibt die längste Anfangsphase zurück."""
    laengste = 0
    for n in range(1, grenze):
        f = folge(n)
        k = drei_phase(n)
        assert all(x % 3 for x in f[k:]), n
        assert all(f[i] == n >> i for i in range(k)), n
        laengste = max(laengste, k)
    return laengste


def main(argv: list[str] | None = None) -> None:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--grenze", type=int, default=100_000)
    a = p.parse_args(argv)
    print(f"Geprüft bis {a.grenze}: längste Phase mit Vielfachen von 3 = {pruefe(a.grenze)}")


if __name__ == "__main__":
    main()
