"""Gibt es ausser 1 → 4 → 2 → 1 weitere Zyklen?

1. Suche: Für alle Startzahlen bis N wird geprüft, ob die Folge in einen anderen
   Zyklus läuft (Ergebnis: nein).
2. Zum Vergleich: Für negative ganze Zahlen gibt es weitere Zyklen!
   (-1, -5, -17 starten drei verschiedene Zyklen.) Ein Beweis der Vermutung muss
   also die Positivität wirklich benutzen.
3. Warum Zyklen schwer sind: Ein Zyklus mit k ungeraden und m geraden Schritten
   braucht 2^m ≈ 3^k, genauer 2^m > 3^k und m/k nahe bei log2(3) = 1.58496...
   Die Kettenbruch-Näherungen von log2(3) zeigen, wie nahe 2^m an 3^k kommen kann.

    python zyklen.py 1000000
"""

from __future__ import annotations

import argparse
import math
from fractions import Fraction


def schritt_z(n: int) -> int:
    """Collatz-Schritt für beliebige ganze Zahlen (auch negativ)."""
    return n // 2 if n % 2 == 0 else 3 * n + 1


def zyklus_von(n: int, limit: int = 10_000) -> tuple[int, ...] | None:
    """Läuft n in einen Zyklus? Gibt den Zyklus (beginnend beim Minimum nach Betrag) zurück."""
    gesehen: dict[int, int] = {}
    x, i = n, 0
    while x not in gesehen and i < limit:
        gesehen[x] = i
        x = schritt_z(x)
        i += 1
    if x not in gesehen:
        return None
    z = [x]
    y = schritt_z(x)
    while y != x:
        z.append(y)
        y = schritt_z(y)
    k = min(range(len(z)), key=lambda j: (abs(z[j]), z[j]))
    return tuple(z[k:] + z[:k])


def zyklen_suchen(von: int, bis: int) -> dict[tuple[int, ...], int]:
    """Alle Zyklen, in die Startzahlen von..bis laufen, mit Anzahl Startzahlen."""
    gefunden: dict[tuple[int, ...], int] = {}
    for n in range(von, bis + 1):
        if n == 0:
            continue
        z = zyklus_von(n)
        if z is not None:
            gefunden[z] = gefunden.get(z, 0) + 1
    return gefunden


def kettenbruch_naeherungen(x: float, anzahl: int) -> list[Fraction]:
    """Die ersten Näherungsbrüche des Kettenbruchs von x."""
    out, a = [], []
    y = x
    for _ in range(anzahl):
        ai = math.floor(y)
        a.append(ai)
        f = Fraction(a[-1])
        for aj in reversed(a[:-1]):
            f = aj + 1 / f
        out.append(f)
        if y - ai < 1e-12:
            break
        y = 1 / (y - ai)
    return out


def main(argv: list[str] | None = None) -> None:
    p = argparse.ArgumentParser(description="Zyklen-Analyse")
    p.add_argument("bis", type=int, nargs="?", default=100000)
    a = p.parse_args(argv)

    print(f"Positive Startzahlen 1..{a.bis}:")
    for z, c in zyklen_suchen(1, a.bis).items():
        print(f"  Zyklus {z}: {c} Startzahlen")

    print("Negative Startzahlen -1000..-1:")
    for z, c in sorted(zyklen_suchen(-1000, -1).items(), key=lambda kv: -kv[1]):
        print(f"  Zyklus der Länge {len(z)}: {z[:6]}{' …' if len(z) > 6 else ''} ({c} Startzahlen)")

    print("Näherungen m/k für log2(3) = 1.5849625…  (Zyklus bräuchte 2^m ≈ 3^k):")
    for f in kettenbruch_naeherungen(math.log2(3), 10):
        m, k = f.numerator, f.denominator
        if k == 0:
            continue
        print(f"  m/k = {m}/{k}:  2^m / 3^k = {2.0 ** (m - k * math.log2(3)):.6f}")


if __name__ == "__main__":
    main()
