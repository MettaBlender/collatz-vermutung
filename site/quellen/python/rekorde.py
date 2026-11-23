"""Rekorde einer Collatz-Folge (Lean: Records.lean, Satz 42).

Ein Rekord ist ein Glied, das grösser ist als alle früheren. Jeder Rekord entsteht als 3x + 1
aus einem ungeraden x und ist daher ≡ 4 (mod 6). Eine divergente Folge hätte unendlich viele.

    python rekorde.py
"""

from __future__ import annotations


def step(n: int) -> int:
    return n // 2 if n % 2 == 0 else 3 * n + 1


def rekorde(n: int, schritte: int = 10 ** 5) -> list[tuple[int, int, int]]:
    """Liste (Index k, Vorgänger x, Rekord) der Rekorde der Folge von n."""
    out, x, best = [], n, n
    for k in range(1, schritte + 1):
        y = step(x)
        if y > best:
            out.append((k, x, y))
            best = y
        if y == 1:
            break
        x = y
    return out


if __name__ == "__main__":
    for n in (27, 703, 77031):
        r = rekorde(n)
        assert all(x % 2 == 1 and y == 3 * x + 1 and y % 6 == 4 for _, x, y in r)
        print(f"n = {n}: {len(r)} Rekorde, letzter {r[-1][2]} (≡ {r[-1][2] % 6} mod 6)")
