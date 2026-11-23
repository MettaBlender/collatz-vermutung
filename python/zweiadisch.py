"""Rückwärtsbaum und 2-adische Paritätsfolgen (Lean: InverseTree.lean, TwoAdic.lean).

1. Jedes n, das nicht durch 3 teilbar ist, hat unendlich viele ungerade Vorfahren
   m = (2^e·n − 1)/3 (mit 2^e·n ≡ 4 mod 6).
2. Jede 0/1-Folge ist die Paritätsfolge genau einer 2-adischen Zahl. Aus den ersten k Paritäten
   berechnet man den Rest modulo 2^k. Für natürliche Zahlen werden die Reste irgendwann
   konstant, für andere Folgen (z. B. 1, 1, 1, …, das ist −1) nicht.
3. Collatz-Vermutung ⇔ jede Paritätsfolge endet in 1, 0, 1, 0, …

    python zweiadisch.py
"""

from __future__ import annotations


def T(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def paritaeten(n: int, k: int) -> list[int]:
    """Die ersten k Paritäten von n unter T (1 = ungerade)."""
    p = []
    for _ in range(k):
        p.append(n % 2)
        n = T(n)
    return p


def aus_paritaeten(bits: list[int]) -> int:
    """Der eindeutige Rest r < 2^k mit den Paritäten bits (Satz von Terras, konstruktiv)."""
    r = 0
    for k in range(len(bits)):
        # r hat die richtigen ersten k Paritäten; genau eine der Hochhebungen r, r + 2^k passt.
        if paritaeten(r, k + 1) != bits[: k + 1]:
            r += 2 ** k
        assert paritaeten(r, k + 1) == bits[: k + 1]
    return r


def vorfahren(n: int, anzahl: int) -> list[int]:
    """Die ersten ungeraden Vorfahren (2^e·n − 1)/3 von n (n nicht durch 3 teilbar)."""
    assert n % 3 != 0
    ergebnis = []
    e = 1
    while len(ergebnis) < anzahl:
        x = 2 ** e * n
        if x % 6 == 4:
            ergebnis.append((x - 1) // 3)
        e += 1
    return ergebnis


def erreicht(m: int, n: int, schritte: int = 10 ** 5) -> bool:
    """Erreicht die Collatz-Folge (3n+1, n/2) von m die Zahl n?"""
    for _ in range(schritte):
        if m == n:
            return True
        m = m // 2 if m % 2 == 0 else 3 * m + 1
    return False


def endet_in_eins_null(n: int, k: int = 400) -> bool:
    """Endet die Paritätsfolge von n (innerhalb von k Schritten) in 1, 0, 1, 0, …?"""
    p = paritaeten(n, k)
    return p[-20:] == [1, 0] * 10 or p[-20:] == [0, 1] * 10


def main() -> None:
    print("Ungerade Vorfahren von 1:", vorfahren(1, 6))
    print("Ungerade Vorfahren von 5:", vorfahren(5, 6))
    print("Ungerade Vorfahren von 7:", vorfahren(7, 6))
    print()
    print("Reste modulo 2^k aus den ersten k Paritäten:")
    for name, folge in [("1,0,1,0,… (die Zahl 1)", [1, 0] * 16),
                        ("1,1,1,…   (die 2-adische −1)", [1] * 32),
                        ("Paritäten von 27", paritaeten(27, 32))]:
        reste = [aus_paritaeten(folge[:k]) for k in (4, 8, 16, 32)]
        print(f"  {name:32s} k=4,8,16,32: {reste}")
    print()
    print("Paritätsfolgen enden in 1,0,1,0,… für alle n < 10 000:",
          all(endet_in_eins_null(n) for n in range(1, 10000)))


if __name__ == "__main__":
    main()
