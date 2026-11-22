"""Die Zyklusgleichung: jeder Zyklus ist durch seinen Paritätsvektor festgelegt.

Mit T(n) = n/2 (gerade) bzw. (qn+1)/2 (ungerade) gilt nach p Schritten mit o ungeraden

    2^p · T^p(n) = q^o · n + c,     c = Σ_{i ungerade Stelle} q^(Anzahl Einsen nach i) · 2^i.

Ein Zyklus (T^p(n) = n) erfüllt also n · (2^p − q^o) = c, d.h. n = c / (2^p − q^o).
In Lean bewiesen für q = 3 (Satz 14, `cycle_equation` in lean/Collatz/Terras.lean).

Das Skript geht alle 2^p Paritätsvektoren durch und sucht ganzzahlige Lösungen n,
deren Bahn den Vektor wirklich durchläuft. Für q = 3 findet man nur den trivialen
Zyklus 1 → 2 → 1 (und seine Wiederholungen), für q = 5 die Zyklen 1 → 3 → 8 → 4 → 2 → 1,
13 → … und 17 → … .

    python zyklus_gleichung.py 20
    python zyklus_gleichung.py 20 --q 5
"""

from __future__ import annotations

import argparse


def T(n: int, q: int = 3) -> int:
    return n // 2 if n % 2 == 0 else (q * n + 1) // 2


def vektor(n: int, p: int, q: int = 3) -> tuple[int, ...]:
    v = []
    for _ in range(p):
        v.append(n % 2)
        n = T(n, q)
    return tuple(v)


def zyklen_aus_vektoren(p_max: int, q: int = 3) -> dict[int, set[int]]:
    """Für jede Länge p ≤ p_max: alle positiven n mit T^p(n) = n (über die Zyklusgleichung)."""
    erg: dict[int, set[int]] = {}
    paare = [(0, 0, ())]  # (o, c, Vektor) für die bisherigen Endstücke
    for p in range(1, p_max + 1):
        neu = []
        for o, c, v in paare:
            neu.append((o, 2 * c, (0,) + v))           # gerade Stelle vorne
            neu.append((o + 1, q**o + 2 * c, (1,) + v))  # ungerade Stelle vorne
        paare = neu
        loesungen = set()
        for o, c, v in paare:
            d = 2**p - q**o
            if d > 0 and c % d == 0 and c > 0:
                n = c // d
                if vektor(n, p, q) == v:  # die Bahn von n läuft wirklich so
                    loesungen.add(n)
        erg[p] = loesungen
    return erg


def main(argv: list[str] | None = None) -> None:
    a = argparse.ArgumentParser(description="Zyklen über die Zyklusgleichung suchen")
    a.add_argument("p_max", type=int, nargs="?", default=18)
    a.add_argument("--q", type=int, default=3)
    args = a.parse_args(argv)
    erg = zyklen_aus_vektoren(args.p_max, args.q)
    alle = set()
    for p, ns in erg.items():
        alle |= ns
        print(f"p = {p:2d}: {2**p:>8} Vektoren, periodische Startwerte: {sorted(ns)}")
    print(f"\n{args.q}n+1: alle Zahlen auf Zyklen mit Periode ≤ {args.p_max}: {sorted(alle)}")


if __name__ == "__main__":
    main()
