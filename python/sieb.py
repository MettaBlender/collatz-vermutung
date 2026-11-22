"""Restklassen-Sieb: welcher Anteil der Zahlen fällt garantiert ab?

Für jede Restklasse r mod 2^k wird symbolisch geprüft, ob alle Zahlen n = 2^k·a + r
unter ihren Startwert fallen. Nur die "Überlebenden" müssen noch untersucht werden.
Derselbe Algorithmus ist in Lean bewiesen (lean/Collatz/Sieve.lean).

    python sieb.py              # bis k = 24, zeigt Diagramm
    python sieb.py 24 --ausgabe ../docs/bilder/sieb.png
"""

from __future__ import annotations

import argparse

from collatz_core import sieb_ueberlebende_bis


def main(argv: list[str] | None = None) -> None:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("k", type=int, nargs="?", default=24, help="grösster Exponent (Standard 24)")
    p.add_argument("--ausgabe", default=None)
    a = p.parse_args(argv)

    stufen = sieb_ueberlebende_bis(a.k)
    print(f"{'k':>3} {'2^k':>12} {'offen':>10} {'Anteil offen':>13}")
    for k, s in enumerate(stufen):
        print(f"{k:>3} {2**k:>12} {len(s):>10} {len(s) / 2**k:>12.4%}")
    print("mod 256 offen:", sorted(stufen[8]) if a.k >= 8 else "-")

    import matplotlib
    if a.ausgabe:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    ks = list(range(len(stufen)))
    anteil = [len(s) / 2**k for k, s in enumerate(stufen)]
    fig, ax = plt.subplots(figsize=(10, 5))
    ax.plot(ks, [100 * x for x in anteil], "o-", color="tab:purple")
    ax.set_yscale("log")
    ax.set_xlabel("k  (Restklassen modulo 2^k)")
    ax.set_ylabel("Anteil noch offener Restklassen in % (log)")
    ax.set_title("Restklassen-Sieb: der offene Anteil schrumpft, aber nie auf 0")
    for k in (4, 8, 12, 16):
        if k < len(stufen):
            ax.annotate(f"{len(stufen[k])} / {2**k}", (k, 100 * anteil[k]),
                        textcoords="offset points", xytext=(5, 8))
    ax.grid(True, which="both", alpha=0.3)
    fig.tight_layout()
    if a.ausgabe:
        fig.savefig(a.ausgabe, dpi=120)
        print("Bild gespeichert:", a.ausgabe)
    else:
        plt.show()


if __name__ == "__main__":
    main()
