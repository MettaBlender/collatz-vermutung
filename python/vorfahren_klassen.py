"""Vorfahren in jeder Restklasse modulo 2^k (Lean: DenseTree.lean).

Ist n > 0 nicht durch 3 teilbar, so hat n in jeder Restklasse s modulo 2^k einen Vorfahren.
Konstruktion wie im Lean-Beweis:
  y = T^k(s), o = Zahl der ungeraden Schritte. Nach Terras ist T^k(s + 2^k b) = y + 3^o b.
  Gesucht ist 2^m n = y + 3^o b. Das geht, weil 2 Primitivwurzel modulo 3^o ist und
  3 ∤ y (für o ≥ 1). Dann ist m' = s + 2^k b ein Vorfahre von n.
Folgerung: Gäbe es ein Gegenbeispiel, dann gäbe es eines in jeder Restklasse modulo 2^k.

    python vorfahren_klassen.py
"""

from __future__ import annotations


def T(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def T_iter(k: int, n: int) -> tuple[int, int]:
    """(T^k(n), Zahl der ungeraden Schritte)."""
    o = 0
    for _ in range(k):
        o += n % 2
        n = T(n)
    return n, o


def ist_primitivwurzel(j: int) -> bool:
    """Erzeugt 2 alle zu 3 teilerfremden Reste modulo 3^j?"""
    M = 3 ** j
    reste, x = set(), 1
    for _ in range(2 * 3 ** (j - 1)):
        reste.add(x)
        x = 2 * x % M
    return len(reste) == 2 * 3 ** (j - 1)


def vorfahre(n: int, k: int, s: int) -> int:
    """Ein m ≡ s (mod 2^k), dessen Folge n erreicht (Konstruktion aus dem Lean-Beweis)."""
    assert n > 0 and n % 3 != 0
    s %= 2 ** k
    y, o = T_iter(k, s)
    m = 0
    while not (2 ** m * n >= y and (2 ** m * n - y) % 3 ** o == 0):
        m += 1
    b = (2 ** m * n - y) // 3 ** o
    return s + 2 ** k * b


def vorfahre_mod3(n: int, k: int, s: int, t: int, grenze: int = 10 ** 7) -> int:
    """Kleinster Vorfahre m von n mit m ≡ s (mod 2^k) und m ≡ t (mod 3) (Lean: DenseTree3.lean)."""
    M = 3 * 2 ** k
    r = next(x for x in range(M) if x % 2 ** k == s % 2 ** k and x % 3 == t % 3)
    for m in range(r if r > 0 else M, grenze, M):
        if erreicht(m, n):
            return m
    raise ValueError("nicht gefunden")


def vorfahre_mod6(n: int, k: int, s: int, J: int, t: int) -> int:
    """Ein Vorfahre x von n mit x ≡ s (mod 2^k) und x ≡ t (mod 3^J) (Lean: ThreeAdic.lean).

    Wie im Lean-Beweis: b0 löst s + 2^k b0 ≡ t (mod 3^J); dann 2^m n ≡ y + 3^o b0 (mod 3^(o+J)).
    """
    assert n > 0 and n % 3 != 0
    s %= 2 ** k
    y, o = T_iter(k, s)
    if o == 0:  # verfeinern auf eine Klasse modulo 2^(k+1) mit einem ungeraden Schritt
        if y % 2 == 0:
            s += 2 ** k
        k += 1
        y, o = T_iter(k, s)
    M = 3 ** J
    b0 = (t - s) * pow(2, -k, M) % M if J > 0 else 0
    ziel, mod = y + 3 ** o * b0, 3 ** (o + J)
    m = 0
    while not (2 ** m * n >= ziel and (2 ** m * n - ziel) % mod == 0):
        m += 1
    b = (2 ** m * n - y) // 3 ** o
    return s + 2 ** k * b


def erreicht(m: int, n: int) -> bool:
    for _ in range(10 ** 6):
        if m == n:
            return True
        m = T(m)
    return False


def main() -> None:
    print("2 ist Primitivwurzel modulo 3^j für j = 1..8:", all(ist_primitivwurzel(j) for j in range(1, 9)))
    print("Vorfahren der 1 in den Klassen modulo 16:")
    for s in range(16):
        m = vorfahre(1, 4, s)
        print(f"  s = {s:2d}: m = {m:>12d}  (m mod 16 = {m % 16}, erreicht 1: {erreicht(m, 1)})")
    print("Vorfahren von 7 in allen 256 Klassen modulo 2^8 gefunden:",
          all(vorfahre(7, 8, s) % 256 == s and erreicht(vorfahre(7, 8, s), 7) for s in range(256)))

    print("Vorfahren der 1 modulo 3·2^3 = 24 (jede Klasse, auch Vielfache von 3):")
    print("  ", [vorfahre_mod3(1, 3, s, t) for s in range(8) for t in range(3)])


if __name__ == "__main__":
    main()
