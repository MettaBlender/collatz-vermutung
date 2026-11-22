"""Visualisiert, wie oft jede Zahl in Collatz-Folgen vorkommt.

Für jede Startzahl 1, 2, ..., N wird die Collatz-Folge bis zur 1 berechnet:

    n gerade   -> n / 2
    n ungerade -> 3n + 1

Gezählt wird, in wie vielen dieser Folgen eine Zahl m vorkommt (die Startzahl
selbst und die 1 am Ende zählen mit). Die 1 kommt also genau N-mal vor.

Beispiele:
    python collatz_verteilung.py 1000
    python collatz_verteilung.py 100000 --bis 500 --top 25
    python collatz_verteilung.py 10000 --ausgabe verteilung.png
"""

from __future__ import annotations

import argparse
from collections import Counter


def collatz_schritt(n: int) -> int:
    """Ein Schritt der Collatz-Abbildung."""
    return n // 2 if n % 2 == 0 else 3 * n + 1


def collatz_folge(n: int) -> list[int]:
    """Die vollständige Folge von n bis 1 (inklusive beider Enden)."""
    if n < 1:
        raise ValueError("Startzahl muss >= 1 sein")
    folge = [n]
    while n != 1:
        n = collatz_schritt(n)
        folge.append(n)
    return folge


def besuche_naiv(ziel: int) -> Counter[int]:
    """Einfache, langsame Referenz: jede Folge komplett ablaufen."""
    zaehler: Counter[int] = Counter()
    for start in range(1, ziel + 1):
        zaehler.update(collatz_folge(start))
    return zaehler


def besuche_zaehlen(ziel: int) -> dict[int, int]:
    """Wie oft kommt jede Zahl in den Folgen der Startzahlen 1..ziel vor?

    Schnelle Variante: Alle Folgen zusammen bilden einen Baum mit Wurzel 1
    (jede Zahl m hat genau einen Nachfolger collatz_schritt(m)). Eine Zahl m
    kommt genau in den Folgen der Startzahlen vor, die im Teilbaum unter m
    liegen. Wir bauen den Baum also einmal auf und summieren dann von den
    Blättern zur Wurzel hoch. So wird jede Zahl nur einmal besucht.
    """
    if ziel < 1:
        raise ValueError("Zielzahl muss >= 1 sein")

    tiefe: dict[int, int] = {1: 0}  # Schritte bis zur 1
    for start in range(2, ziel + 1):
        pfad = []
        n = start
        while n not in tiefe:
            pfad.append(n)
            n = collatz_schritt(n)
        t = tiefe[n]
        for m in reversed(pfad):
            t += 1
            tiefe[m] = t

    anzahl = {m: 0 for m in tiefe}
    for start in range(1, ziel + 1):
        anzahl[start] = 1

    # Von tief nach flach: jede Zahl gibt ihre Anzahl an den Nachfolger weiter.
    for m in sorted(tiefe, key=tiefe.__getitem__, reverse=True):
        if m != 1:
            anzahl[collatz_schritt(m)] += anzahl[m]
    return anzahl


def zeichnen(anzahl: dict[int, int], ziel: int, bis: int, top: int, ausgabe: str | None) -> None:
    import matplotlib

    if ausgabe:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, (ax1, ax2, ax3) = plt.subplots(3, 1, figsize=(12, 13))
    fig.suptitle(f"Collatz: wie oft wird jede Zahl besucht? (Startzahlen 1 bis {ziel:,})".replace(",", "'"))

    # 1) Besuche pro Zahl für die Zahlen 1..bis
    xs = list(range(1, bis + 1))
    ys = [anzahl.get(x, 0) for x in xs]
    farben = ["tab:blue" if x % 2 == 0 else "tab:orange" for x in xs]
    ax1.bar(xs, ys, color=farben, width=1.0)
    ax1.set_yscale("log")
    ax1.set_xlabel("Zahl")
    ax1.set_ylabel("Anzahl Besuche (log)")
    ax1.set_title(f"Besuche pro Zahl von 1 bis {bis} (blau = gerade, orange = ungerade)")

    # 2) Die meistbesuchten Zahlen
    haeufigste = sorted(anzahl.items(), key=lambda kv: (-kv[1], kv[0]))[:top]
    ax2.bar([str(m) for m, _ in haeufigste], [c for _, c in haeufigste], color="tab:green")
    ax2.set_ylabel("Anzahl Besuche")
    ax2.set_title(f"Die {len(haeufigste)} meistbesuchten Zahlen")
    ax2.tick_params(axis="x", rotation=60)

    # 3) Wie viele Zahlen werden genau k-mal besucht?
    verteilung = Counter(anzahl.values())
    ks = sorted(verteilung)
    ax3.scatter(ks, [verteilung[k] for k in ks], s=8)
    ax3.set_xscale("log")
    ax3.set_yscale("log")
    ax3.set_xlabel("k = Anzahl Besuche")
    ax3.set_ylabel("Wie viele Zahlen (log)")
    ax3.set_title(f"Verteilung der Besuchszahlen ({len(anzahl):,} verschiedene Zahlen kommen vor)".replace(",", "'"))

    fig.tight_layout()
    if ausgabe:
        fig.savefig(ausgabe, dpi=120)
        print(f"Bild gespeichert: {ausgabe}")
    else:
        plt.show()


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description="Visualisiert, wie oft jede Zahl in Collatz-Folgen vorkommt.")
    parser.add_argument("ziel", type=int, help="Startzahlen 1 bis ziel werden durchgerechnet")
    parser.add_argument("--bis", type=int, default=None, help="oberes Diagramm zeigt Zahlen 1 bis BIS (Standard: min(ziel, 200))")
    parser.add_argument("--top", type=int, default=20, help="wie viele meistbesuchte Zahlen gezeigt werden (Standard: 20)")
    parser.add_argument("--ausgabe", default=None, help="Bild in diese Datei speichern statt Fenster öffnen, z.B. bild.png")
    args = parser.parse_args(argv)

    if args.ziel < 1:
        parser.error("ziel muss >= 1 sein")
    bis = args.bis if args.bis is not None else min(args.ziel, 200)

    anzahl = besuche_zaehlen(args.ziel)

    print(f"Startzahlen 1 bis {args.ziel}: {len(anzahl)} verschiedene Zahlen kommen vor, "
          f"grösste besuchte Zahl: {max(anzahl)}")
    print(f"Die {args.top} meistbesuchten Zahlen:")
    for m, c in sorted(anzahl.items(), key=lambda kv: (-kv[1], kv[0]))[: args.top]:
        print(f"  {m:>10}  {c:>10}x")

    zeichnen(anzahl, args.ziel, bis, args.top, args.ausgabe)


if __name__ == "__main__":
    main()
