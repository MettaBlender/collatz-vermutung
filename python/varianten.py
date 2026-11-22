"""Varianten qn+1: Warum gerade die 3?

Statt 3n+1 nimmt man qn+1 für ungerade n (q ungerade). Für q = 1 und q = 3 landen alle
getesteten Startzahlen bei 1. Schon für q = 5 gibt es weitere Zyklen (13 und 17) und die
meisten Folgen wachsen scheinbar unbegrenzt. Die Heuristik erklärt das: pro ungeradem
Schritt (qn+1, dann /2) und geradem Schritt (/2) wird eine Zahl im Mittel mit q/4
multipliziert. Für q = 3 ist das 3/4 < 1 (fällt), für q = 5 ist es 5/4 > 1 (wächst).

    python varianten.py 2000
    python varianten.py 2000 --ausgabe ../docs/bilder/varianten.png
"""

from __future__ import annotations

import argparse

GRENZE = 10**12  # ab hier zählt eine Folge als "entkommen"


def schritt_q(n: int, q: int) -> int:
    return n // 2 if n % 2 == 0 else q * n + 1


def schicksal(start: int, q: int) -> tuple[str, int]:
    """("eins" | "zyklus" | "entkommen", kleinstes Zyklusglied oder 0)."""
    gesehen = set()
    n = start
    while n not in gesehen:
        if n >= GRENZE:
            return "entkommen", 0
        gesehen.add(n)
        n = schritt_q(n, q)
    zyklus = [n]
    m = schritt_q(n, q)
    while m != n:
        zyklus.append(m)
        m = schritt_q(m, q)
    lo = min(zyklus)
    return ("eins" if lo == 1 else "zyklus"), lo


def zyklus_von(n: int, q: int) -> list[int]:
    z = [n]
    m = schritt_q(n, q)
    while m != n:
        z.append(m)
        m = schritt_q(m, q)
    return z


def auswerten(bis: int, qs=(1, 3, 5, 7, 9)) -> dict[int, dict]:
    erg = {}
    for q in qs:
        zaehler = {"eins": 0, "zyklus": 0, "entkommen": 0}
        zyklen = set()
        for s in range(1, bis + 1):
            art, lo = schicksal(s, q)
            zaehler[art] += 1
            if lo:
                zyklen.add(lo)
        erg[q] = {"zaehler": zaehler, "zyklen": sorted(zyklen)}
    return erg


def main(argv: list[str] | None = None) -> None:
    p = argparse.ArgumentParser(description="Varianten qn+1 der Collatz-Abbildung")
    p.add_argument("bis", type=int, nargs="?", default=2000)
    p.add_argument("--ausgabe", default=None)
    a = p.parse_args(argv)

    erg = auswerten(a.bis)
    for q, e in erg.items():
        z = e["zaehler"]
        print(f"q={q}: zur 1: {z['eins']}, anderer Zyklus: {z['zyklus']}, entkommen (> 10^12): "
              f"{z['entkommen']}, Zyklen (kleinstes Glied): {e['zyklen']}")
    print("5n+1-Zyklus ab 13:", " → ".join(map(str, zyklus_von(13, 5) + [13])))

    import matplotlib
    if a.ausgabe:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 4.5))
    qs = list(erg)
    unten = [0] * len(qs)
    for art, farbe, name in (("eins", "tab:green", "erreicht 1"), ("zyklus", "tab:orange", "anderer Zyklus"),
                             ("entkommen", "tab:red", "über 10^12")):
        werte = [100 * erg[q]["zaehler"][art] / a.bis for q in qs]
        ax1.bar([f"{q}n+1" for q in qs], werte, bottom=unten, color=farbe, label=name)
        unten = [u + w for u, w in zip(unten, werte)]
    ax1.set_ylabel("Anteil der Startzahlen (%)")
    ax1.set_title(f"Schicksal der Startzahlen 1 bis {a.bis}")
    ax1.legend(loc="upper center", bbox_to_anchor=(0.5, -0.08), ncol=3)

    import math
    for q, farbe in ((3, "tab:green"), (5, "tab:red")):
        n, ys = 7, []
        for _ in range(120):
            ys.append(math.log2(n))
            if n == 1 or n > GRENZE:
                break
            n = schritt_q(n, q)
        ax2.plot(ys, color=farbe, label=f"{q}n+1 ab 7")
    ax2.set_xlabel("Schritt")
    ax2.set_ylabel("log2(Wert)")
    ax2.set_title("Mittlerer Faktor pro Paar: 3/4 < 1 fällt, 5/4 > 1 wächst")
    ax2.legend()
    fig.tight_layout()
    if a.ausgabe:
        fig.savefig(a.ausgabe, dpi=110)
        print("Bild gespeichert:", a.ausgabe)
    else:
        plt.show()


if __name__ == "__main__":
    main()
