"""Der Collatz-Baum: alle Zahlen, die in genau k Schritten bei 1 landen.

Rückwärts gerechnet hat jede Zahl m den Vorgänger 2m, und zusätzlich (m-1)/3,
falls m ≡ 4 (mod 6) und (m-1)/3 > 1. Die Vermutung sagt: dieser Baum enthält
jede positive ganze Zahl.

    python baum.py 18 --ausgabe ../docs/bilder/baum.png
"""

from __future__ import annotations

import argparse


def vorgaenger(m: int) -> list[int]:
    """Alle Zahlen, die in einem Collatz-Schritt zu m führen."""
    v = [2 * m]
    if m % 6 == 4 and (m - 1) // 3 > 1:
        v.append((m - 1) // 3)
    return v


def ebenen(tiefe: int) -> list[list[int]]:
    """ebenen[k] = alle Zahlen mit Gesamtstoppzeit genau k."""
    e = [[1]]
    for _ in range(tiefe):
        e.append(sorted(x for m in e[-1] for x in vorgaenger(m) if x != 1))
    return e


def main(argv: list[str] | None = None) -> None:
    p = argparse.ArgumentParser(description="Collatz-Baum")
    p.add_argument("tiefe", type=int, nargs="?", default=18)
    p.add_argument("--ausgabe", default=None)
    a = p.parse_args(argv)

    e = ebenen(60)
    print("k  Anzahl Zahlen mit Gesamtstoppzeit k   Wachstum")
    for k in range(0, 61, 5):
        w = len(e[k]) / len(e[k - 1]) if k else 0
        print(f"{k:>2}  {len(e[k]):>10}   {w:.3f}")
    print(f"Mittleres Wachstum k=40..60: {(len(e[60]) / len(e[40])) ** (1 / 20):.4f} pro Ebene")
    # Heuristik: G = gerade, U = ungerade Knoten. Jeder Knoten hat das Kind 2m (gerade),
    # etwa 1/3 der geraden Knoten (m ≡ 4 mod 6) zusätzlich ein ungerades Kind.
    # G' = G + U, U' = G/3  =>  λ² = λ + 1/3  =>  λ = (1 + √(7/3)) / 2
    print(f"Heuristik λ = (1 + √(7/3))/2 = {(1 + (7 / 3) ** 0.5) / 2:.4f}")

    import matplotlib
    if a.ausgabe:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6.5), gridspec_kw={"width_ratios": [1.6, 1]})
    # Baum zeichnen: jede Ebene eine Zeile, Kinder unter dem Elternknoten
    pos: dict[int, tuple[float, int]] = {1: (0.0, 0)}
    breite = {1: 1.0}
    ebene = [1]
    for k in range(1, a.tiefe + 1):
        neu = []
        for m in ebene:
            kinder = [x for x in vorgaenger(m) if x != 1]
            x0, _ = pos[m]
            w = breite[m]
            for i, c in enumerate(kinder):
                if len(kinder) == 1:
                    pos[c], breite[c] = (x0, k), w
                else:
                    off = (-0.25 if i == 0 else 0.25) * w
                    pos[c], breite[c] = (x0 + off, k), w / 2
                ax1.plot([x0, pos[c][0]], [-(k - 1), -k], color="tab:blue" if c % 2 == 0 else "tab:orange", lw=0.8)
                neu.append(c)
        ebene = neu
    for m, (x, k) in pos.items():
        if k <= 12 or m % 2 == 1:
            ax1.annotate(str(m), (x, -k), fontsize=6 if k > 10 else 8, ha="center", va="center",
                         bbox=dict(boxstyle="round,pad=0.15", fc="white", ec="none", alpha=0.8))
    ax1.set_title(f"Collatz-Baum bis Tiefe {a.tiefe} (orange: Abzweig über (m-1)/3)")
    ax1.axis("off")

    ks = list(range(len(e)))
    ax2.semilogy(ks, [len(x) for x in e], "o-", ms=3, color="tab:purple", label="Zahlen mit σ∞ = k")
    lam = (1 + (7 / 3) ** 0.5) / 2
    ax2.semilogy(ks, [len(e[40]) * lam ** (k - 40) for k in ks], "--", color="gray",
                 label=f"λ^k mit λ = (1+√(7/3))/2 ≈ {lam:.4f}")
    ax2.set_xlabel("k (Gesamtstoppzeit)")
    ax2.set_ylabel("Anzahl (log)")
    ax2.set_title("Jede Ebene ist etwa 1.264 mal so gross")
    ax2.legend()
    ax2.grid(True, which="both", alpha=0.3)

    fig.tight_layout()
    if a.ausgabe:
        fig.savefig(a.ausgabe, dpi=120)
        print("Bild gespeichert:", a.ausgabe)
    else:
        plt.show()


if __name__ == "__main__":
    main()
