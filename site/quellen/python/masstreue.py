"""T ist masstreu, Vergangenheit und Zukunft sind unabhängig (Lean: Mixing.lean).

Für jedes Paritätsmuster u der Länge j und jeden Rest s < 2^k gibt es genau ein
r < 2^(j+k) mit den ersten j Paritäten u und T^j(r) ≡ s (mod 2^k).
Die ersten j Paritäten verraten also nichts über T^j(n) modulo 2^k.

    python masstreue.py
"""

from __future__ import annotations

from collections import Counter


def T(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def muster_und_rest(r: int, j: int, k: int) -> tuple[tuple[int, ...], int]:
    p = []
    for _ in range(j):
        p.append(r % 2)
        r = T(r)
    return tuple(p), r % 2 ** k


def tabelle(j: int, k: int) -> Counter:
    """Wie oft kommt jedes Paar (Muster, Rest) unter r < 2^(j+k) vor?"""
    return Counter(muster_und_rest(r, j, k) for r in range(2 ** (j + k)))


def urbilder(s: int, k: int) -> list[int]:
    """Alle r < 2^(k+1) mit T(r) ≡ s (mod 2^k)."""
    return [r for r in range(2 ** (k + 1)) if T(r) % 2 ** k == s]


def main() -> None:
    for j, k in [(1, 4), (3, 3), (5, 6), (8, 4)]:
        t = tabelle(j, k)
        print(f"j={j}, k={k}: {len(t)} Paare (= 2^(j+k) = {2 ** (j + k)}), "
              f"jedes genau einmal: {set(t.values()) == {1}}")
    print("Urbilder von s modulo 2^(k+1), k = 5:")
    for s in range(6):
        print(f"  s={s}: {urbilder(s, 5)}")


if __name__ == "__main__":
    main()
