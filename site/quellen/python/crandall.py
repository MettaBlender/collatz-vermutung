"""Viele Zahlen erreichen die 1: ein binärer Baum ungerader Vorfahren (Lean: Crandall.lean).

Jede ungerade Zahl n, die nicht durch 3 teilbar ist, hat zwei kleine ungerade Vorfahren
c mit 3c + 1 = 2^E · n (E <= 6), beide wieder nicht durch 3 teilbar und < 22n. Ab der
Wurzel 5 ergibt das 2^t verschiedene Zahlen <= 5 · 22^t, die alle die 1 erreichen.
Für jedes x erreichen also mindestens etwa (x/5)^(log 2 / log 22) ≈ (x/5)^0.224 Zahlen <= x
die 1. Bewiesen für alle t, ohne Rechnung.

    python crandall.py
"""

from __future__ import annotations

from math import log


def c0(n: int) -> int:
    return (4 * n - 1) // 3 if n % 3 == 1 else (2 * n - 1) // 3


def child(n: int, b: bool) -> int:
    c = c0(n)
    if b:
        return 4 * c + 1 if c % 3 == 1 else 16 * c + 5
    return 4 * c + 1 if c % 3 == 0 else c


def node(t: int, k: int) -> int:
    """Knoten des Baums: Die Bits von k (niedrigstes zuerst, nahe den Blättern) wählen den Weg."""
    if t == 0:
        return 5
    return child(node(t - 1, k // 2), k % 2 == 1)


def erreicht_eins(n: int, schritte: int = 10 ** 6) -> bool:
    for _ in range(schritte):
        if n == 1:
            return True
        n = n // 2 if n % 2 == 0 else 3 * n + 1
    return False


def ebene(t: int) -> list[int]:
    return [node(t, k) for k in range(2 ** t)]


def main() -> None:
    print("Kinder von 5:", child(5, False), child(5, True))
    print(" t   Knoten 2^t   verschieden   max <= 5·22^t   alle erreichen 1")
    for t in range(0, 13):
        e = ebene(t)
        print(f"{t:2d}   {len(e):9d}   {len(set(e)) == len(e)!s:>11}   "
              f"{max(e) <= 5 * 22 ** t!s:>13}   {all(erreicht_eins(n) for n in e)}")
    print()
    print(f"Exponent der unteren Schranke: log 2 / log 22 = {log(2) / log(22):.3f}"
          " (Krasikov–Lagarias: 0.84, Vermutung: 1)")


if __name__ == "__main__":
    main()
