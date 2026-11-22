"""Gemeinsame Grundfunktionen für alle Collatz-Skripte."""

from __future__ import annotations


def schritt(n: int) -> int:
    """Ein Collatz-Schritt: n/2 für gerade n, sonst 3n+1."""
    return n // 2 if n % 2 == 0 else 3 * n + 1


def folge(n: int) -> list[int]:
    """Die Folge von n bis 1 (beide Enden inklusive)."""
    if n < 1:
        raise ValueError("n muss >= 1 sein")
    f = [n]
    while n != 1:
        n = schritt(n)
        f.append(n)
    return f


def gesamtstoppzeit(n: int) -> int:
    """Anzahl Schritte, bis die 1 erreicht ist (σ∞)."""
    k = 0
    while n != 1:
        n = schritt(n)
        k += 1
    return k


def stoppzeit(n: int) -> int:
    """Anzahl Schritte, bis die Folge zum ersten Mal unter n fällt (σ). Für n = 1: 0."""
    if n <= 1:
        return 0
    x, k = n, 0
    while x >= n:
        x = schritt(x)
        k += 1
    return k


def gesamtstoppzeiten(bis: int) -> list[int]:
    """σ∞(n) für alle 0 ≤ n ≤ bis (Index 0 ungenutzt), mit Zwischenspeicher."""
    t = [0] * (bis + 1)
    for start in range(2, bis + 1):
        x, k = start, 0
        while x >= start:  # alle kleineren Werte sind schon bekannt
            x = schritt(x)
            k += 1
        t[start] = k + t[x]
    return t


def maximum(n: int) -> int:
    """Grösster Wert der Folge ab n."""
    m = n
    while n != 1:
        n = schritt(n)
        m = max(m, n)
    return m


def sieb_check(N: int, r: int, fuel: int = 200) -> bool:
    """Gleicher Algorithmus wie `Collatz.check` in Lean (lean/Collatz/Sieve.lean).

    True heisst: jede Zahl n = N·a + r (n > 1) fällt garantiert unter ihren Startwert.
    """
    M, s = N, r
    for _ in range(fuel):
        if M < N and (s < r or (s <= r and r <= 1)):
            return True
        if M % 2:
            return False
        if s % 2 == 0:
            M, s = M // 2, s // 2
        else:
            M, s = 3 * M, 3 * s + 1
    return False


def sieb_ueberlebende(k: int) -> list[int]:
    """Restklassen modulo 2^k, die das Sieb nicht erledigt."""
    N = 2**k
    return [r for r in range(N) if not sieb_check(N, r)]


def sieb_ueberlebende_bis(k_max: int) -> list[list[int]]:
    """Überlebende Restklassen für k = 0..k_max, rekursiv berechnet.

    Ist die Klasse r mod 2^k erledigt, dann auch ihre beiden Teilklassen
    r und r + 2^k mod 2^(k+1). Man muss also nur die Überlebenden weiter aufteilen.
    """
    stufen = [[0]]  # mod 1: alles offen
    for k in range(1, k_max + 1):
        N = 2**k
        kandidaten = [r + j * (N // 2) for r in stufen[-1] for j in (0, 1)]
        stufen.append([r for r in kandidaten if not sieb_check(N, r)])
    return stufen
