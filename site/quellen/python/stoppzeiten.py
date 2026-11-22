"""Stoppzeiten und Rekorde.

- Gesamtstoppzeit σ∞(n): Schritte bis zur 1
- Stoppzeit σ(n): Schritte, bis die Folge zum ersten Mal unter n fällt
- Rekorde: Startzahlen, die länger brauchen als alle kleineren

    python stoppzeiten.py 100000
    python stoppzeiten.py 100000 --ausgabe ../docs/bilder/stoppzeiten.png
"""

from __future__ import annotations

import argparse
import math
from collections import Counter

from collatz_core import gesamtstoppzeiten, maximum, stoppzeit


def rekorde(werte: list[int]) -> list[tuple[int, int]]:
    """(n, wert) für alle n, bei denen werte[n] grösser als alle früheren ist."""
    out, best = [], -1
    for n in range(1, len(werte)):
        if werte[n] > best:
            best = werte[n]
            out.append((n, best))
    return out


def main(argv: list[str] | None = None) -> None:
    p = argparse.ArgumentParser(description="Stoppzeiten und Rekorde")
    p.add_argument("bis", type=int, nargs="?", default=100000)
    p.add_argument("--ausgabe", default=None)
    a = p.parse_args(argv)

    t = gesamtstoppzeiten(a.bis)
    s = [0] + [stoppzeit(n) for n in range(1, a.bis + 1)]

    print("Rekorde der Gesamtstoppzeit σ∞ (n, Schritte, Maximum der Folge):")
    for n, v in rekorde(t):
        print(f"  {n:>8} {v:>5} {maximum(n):>14}")
    mittel = sum(t[1:]) / a.bis
    print(f"Mittlere Gesamtstoppzeit bis {a.bis}: {mittel:.1f} "
          f"(≈ {mittel / math.log(a.bis):.2f} · ln N)")

    import matplotlib
    if a.ausgabe:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, axs = plt.subplots(2, 2, figsize=(13, 9))
    ns = range(1, a.bis + 1)

    ax = axs[0][0]
    ax.scatter(ns, t[1:], s=0.2, color="tab:blue", alpha=0.5)
    xs = [x for x in ns if x > 1][:: max(1, a.bis // 500)]
    ax.plot(xs, [10.41 * math.log(x) for x in xs], color="tab:red", lw=1,
            label="10.41 · ln n (heuristische Erwartung)")
    ax.set_title("Gesamtstoppzeit σ∞(n)")
    ax.set_xlabel("n")
    ax.set_ylabel("Schritte bis 1")
    ax.legend()

    ax = axs[0][1]
    c = Counter(t[1:])
    ax.bar(list(c), list(c.values()), width=1, color="tab:blue")
    ax.set_title(f"Häufigkeit der Gesamtstoppzeiten (n ≤ {a.bis:,})".replace(",", "'"))
    ax.set_xlabel("Schritte bis 1")
    ax.set_ylabel("Anzahl Startzahlen")

    ax = axs[1][0]
    c = Counter(s[2:])
    keys = sorted(c)
    ax.bar([str(k) for k in keys], [c[k] for k in keys], color="tab:green")
    ax.set_yscale("log")
    ax.set_title("Stoppzeit σ(n): nur die Werte 1, 3, 6, 8, 11, 13, 16, … kommen vor")
    ax.set_xlabel("σ(n)")
    ax.set_ylabel("Anzahl (log)")
    ax.tick_params(axis="x", rotation=90, labelsize=7)

    ax = axs[1][1]
    rk = rekorde(t)
    ax.plot([n for n, _ in rk], [v for _, v in rk], "o-", color="tab:orange")
    for n, v in rk[-4::2]:
        ax.annotate(str(n), (n, v), textcoords="offset points", xytext=(-10, 6), fontsize=8)
    ax.set_xscale("log")
    ax.set_title("Rekordhalter der Gesamtstoppzeit")
    ax.set_xlabel("n (log)")
    ax.set_ylabel("σ∞(n)")

    fig.tight_layout()
    if a.ausgabe:
        fig.savefig(a.ausgabe, dpi=110)
        print("Bild gespeichert:", a.ausgabe)
    else:
        plt.show()


if __name__ == "__main__":
    main()
