"""Trajektorien: wie sehen einzelne Collatz-Folgen aus?

Links: einige berühmte Folgen (log-Skala). Rechts: log2 der Werte, verglichen mit
der Heuristik "Zufallsweg mit Drift". Im Mittel wird eine Zahl pro ungeradem Schritt
(3n+1, dann /2) mit 3/2 und pro geradem Schritt mit 1/2 multipliziert, also pro
Paar mit 3/4 < 1: die Folgen fallen im Mittel.

    python trajektorien.py 27 97 871
    python trajektorien.py --ausgabe ../docs/bilder/trajektorien.png
"""

from __future__ import annotations

import argparse
import math
import random

from collatz_core import folge, schritt


def kurzfolge(n: int) -> list[int]:
    """Folge der beschleunigten Abbildung T(n) = n/2 bzw. (3n+1)/2."""
    f = [n]
    while n != 1:
        n = n // 2 if n % 2 == 0 else (3 * n + 1) // 2
        f.append(n)
    return f


def main(argv: list[str] | None = None) -> None:
    p = argparse.ArgumentParser(description="Collatz-Trajektorien")
    p.add_argument("zahlen", type=int, nargs="*", default=[27, 97, 871, 77031])
    p.add_argument("--ausgabe", default=None)
    a = p.parse_args(argv)

    import matplotlib
    if a.ausgabe:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5.5))
    for n in a.zahlen:
        f = folge(n)
        print(f"{n}: {len(f) - 1} Schritte, Maximum {max(f)}")
        ax1.plot(f, lw=1, label=f"n = {n} ({len(f) - 1} Schritte)")
    ax1.set_yscale("log")
    ax1.set_xlabel("Schritt")
    ax1.set_ylabel("Wert (log)")
    ax1.set_title("Collatz-Folgen")
    ax1.legend()

    random.seed(1)
    start_bits = 60
    for i in range(12):
        n = random.getrandbits(start_bits) | (1 << (start_bits - 1))
        f = kurzfolge(n)
        ax2.plot([math.log2(x) for x in f], lw=0.8, alpha=0.7)
    steps = range(0, 290)
    drift = 0.5 * math.log2(3 / 4)
    ax2.plot(steps, [start_bits + drift * k for k in steps], "k--", lw=2,
             label=f"Erwartung: {drift:.3f} Bit pro Schritt")
    ax2.set_ylim(bottom=0)
    ax2.set_xlabel("Schritt der Abbildung T(n) = n/2 bzw. (3n+1)/2")
    ax2.set_ylabel("log2(Wert)")
    ax2.set_title("12 zufällige 60-Bit-Startzahlen: Zufallsweg mit negativer Drift")
    ax2.legend()

    fig.tight_layout()
    if a.ausgabe:
        fig.savefig(a.ausgabe, dpi=110)
        print("Bild gespeichert:", a.ausgabe)
    else:
        plt.show()


if __name__ == "__main__":
    main()
