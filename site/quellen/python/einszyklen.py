"""Keine 1-Zyklen (Steiner 1977) mit wenigen ungeraden Schritten.

Ein 1-Zyklus besteht aus o ungeraden Schritten von T(n) = (3n+1)/2 am Stück und dann e
Halbierungen. Für ihn gilt die Zyklusgleichung n · (2^(o+e) − 3^o) = 3^o − 2^o (in Lean
bewiesen: `one_cycle_equation`). Da jeder weitere Zyklus nur Zahlen ≥ 2^22 enthält, müsste
(2^(o+e) − 3^o) · 2^22 ≤ 3^o − 2^o sein, also 3^o extrem nahe unter einer Zweierpotenz.

Das Skript prüft das für alle o ≤ N mit der kleinsten Zweierpotenz über 3^o (grössere
Zweierpotenzen machen den Abstand nur grösser). Lean prüft es bis 30 000.

    python einszyklen.py 200000
"""

from __future__ import annotations

import argparse


def kritische_o(n_max: int, schranke: int = 2**22) -> list[int]:
    """Alle o ≤ n_max, für die (2^m − 3^o)·schranke ≤ 3^o − 2^o mit kleinstem m gilt."""
    treffer = []
    t, w, e = 1, 1, 2  # 3^o, 2^o, kleinste Zweierpotenz > 3^o
    for o in range(1, n_max + 1):
        t, w = 3 * t, 2 * w
        while e <= t:
            e *= 2
        if (e - t) * schranke <= t - w:
            treffer.append(o)
    return treffer


def naechster_abstand(n_max: int) -> tuple[int, float]:
    """Das o ≤ n_max, bei dem 3^o relativ am nächsten unter einer Zweierpotenz liegt."""
    from math import log2
    bestes, wert = 0, 1.0
    for o in range(1, n_max + 1):
        x = o * log2(3)
        abstand = 1 - (x - int(x))  # wie weit log2(3^o) unter der nächsten ganzen Zahl liegt
        if abstand < wert:
            bestes, wert = o, abstand
    return bestes, wert


def main(argv: list[str] | None = None) -> None:
    a = argparse.ArgumentParser(description="1-Zyklen ausschliessen")
    a.add_argument("n_max", type=int, nargs="?", default=100000)
    args = a.parse_args(argv)
    t = kritische_o(args.n_max)
    print(f"o ≤ {args.n_max}: kritische o (wo ein 1-Zyklus ≥ 2^22 möglich wäre): {t or 'keine'}")
    o, d = naechster_abstand(args.n_max)
    print(f"am knappsten: o = {o}, log2(3^o) liegt {d:.2e} unter einer ganzen Zahl "
          f"(nötig wäre etwa {2.0**-22:.1e} · 2^(-o))")


if __name__ == "__main__":
    main()
