"""Paritätsvektoren und warum das Sieb nie fertig wird (Satz von Terras).

Für die beschleunigte Abbildung T(n) = n/2 bzw. (3n+1)/2 bestimmen die ersten k
Paritäten (gerade/ungerade) eindeutig die Restklasse n mod 2^k, und umgekehrt:
jede der 2^k möglichen 0/1-Folgen kommt genau einmal vor (Terras 1976).

Hat ein Paritätsvektor j Einsen (ungerade Schritte), so ist nach k Schritten
T^k(n) ≈ n · 3^j / 2^k. Abstieg ist garantiert, sobald 3^j < 2^k, also j < k·log_3(2).
Zählt man die 0/1-Folgen der Länge k, bei denen kein Anfangsstück 3^j < 2^i erfüllt,
erhält man (für alle geprüften k) exakt den offenen Anteil des Restklassen-Siebs:
Nach Terras entspricht jede Restklasse genau einer 0/1-Folge. Dieser Anteil geht
gegen 0 (wie beim Münzwurf: zu viele Einsen werden immer seltener), aber nie auf 0.

    python paritaet.py 20 --ausgabe ../docs/bilder/paritaet.png
"""

from __future__ import annotations

import argparse
import math

from collatz_core import sieb_ueberlebende_bis


def T(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def paritaetsvektor(n: int, k: int) -> tuple[int, ...]:
    v = []
    for _ in range(k):
        v.append(n % 2)
        n = T(n)
    return tuple(v)


def ist_bijektion(k: int) -> bool:
    """Prüft den Satz von Terras für k: r ↦ Paritätsvektor ist bijektiv auf {0..2^k-1}."""
    return len({paritaetsvektor(r, k) for r in range(2**k)}) == 2**k


def restklasse_von(vektor) -> int:
    """Die eindeutige Restklasse r < 2^k mit Paritätsvektor `vektor` (Konstruktion wie in Lean).

    Von hinten nach vorne: Ist r die Klasse für den Rest des Vektors (modulo 2^(k-1)), so
    nimmt man für eine 0 die Zahl 2r und für eine 1 die Zahl 2x+1 mit 3x+2 ≡ r (mod 2^(k-1)),
    also x = 3^(-1)·(r − 2) modulo 2^(k-1).
    """
    r = 0
    for i, b in enumerate(reversed(list(vektor))):
        K = 2**i  # r ist bisher modulo K bestimmt
        if b:
            x = (pow(3, -1, K) * (r - 2)) % K if K > 1 else 0
            r = 2 * x + 1
        else:
            r = 2 * r
    return r


def ausnahmen(k: int) -> int:
    """Anzahl der Klassen r < 2^k mit 2·3^o > 2^k (o = ungerade Schritte), wie `badCount` in Lean.

    Nach Terras hat genau C(k, o) der Klassen o ungerade Schritte, also ist das eine
    Binomialsumme. Alle anderen Zahlen n ≥ 2^k fallen beweisbar ab (Satz 15).
    """
    from math import comb
    return sum(comb(k, o) for o in range(k + 1) if 2 * 3**o > 2**k)


def binomial_offen(k: int) -> float:
    """Anteil der 0/1-Folgen der Länge k, bei denen kein Präfix 3^j < 2^i erfüllt."""
    # Dynamische Programmierung über Präfixe: Ein Pfad ist "erledigt", sobald für ein
    # Präfix der Länge i mit j Einsen gilt 3^j < 2^i.
    offen = {0: 1.0}  # Anzahl Einsen -> Wahrscheinlichkeit, noch offen
    for i in range(1, k + 1):
        neu: dict[int, float] = {}
        for j, p in offen.items():
            for b in (0, 1):
                jj = j + b
                if jj * math.log2(3) < i:  # abgestiegen
                    continue
                neu[jj] = neu.get(jj, 0.0) + p / 2
        offen = neu
    return sum(offen.values())


def main(argv: list[str] | None = None) -> None:
    p = argparse.ArgumentParser(description="Paritätsvektoren")
    p.add_argument("k", type=int, nargs="?", default=20)
    p.add_argument("--ausgabe", default=None)
    a = p.parse_args(argv)

    for k in range(1, 17):
        assert ist_bijektion(k)
    print("Satz von Terras für k = 1..16 nachgeprüft: jede Paritätsfolge kommt genau einmal vor.")
    print("Beispiel k=4:", {r: "".join(map(str, paritaetsvektor(r, 4))) for r in range(16)})

    # Das Sieb in Python arbeitet mit der Standardabbildung, 2^k ↔ k Halbierungen.
    stufen = sieb_ueberlebende_bis(a.k)
    print(f"{'k':>3} {'Sieb offen':>12} {'0/1-Folgen':>16}")
    tats, mod = [], []
    for k in range(1, a.k + 1):
        t = len(stufen[k]) / 2**k
        m = binomial_offen(k)
        tats.append(t)
        mod.append(m)
        print(f"{k:>3} {t:>11.4%} {m:>15.4%}")

    import matplotlib
    if a.ausgabe:
        matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13, 5))
    ks = list(range(1, a.k + 1))
    ax1.semilogy(ks, [100 * x for x in tats], "o-", color="tab:purple", label="Sieb (exakt, wie in Lean)")
    ax1.semilogy(ks, [100 * x for x in mod], "s--", color="tab:green", label="Zählung der 0/1-Folgen")
    ax1.set_xlabel("k")
    ax1.set_ylabel("offener Anteil in % (log)")
    ax1.set_title("Sieb = Zählung von Paritätsfolgen (exakt gleich)")
    ax1.legend()
    ax1.grid(True, which="both", alpha=0.3)

    k = 40
    js = list(range(k + 1))
    probs = [math.comb(k, j) / 2**k for j in js]
    grenze = k / math.log2(3)
    ax2.bar(js, probs, color=["tab:green" if j < grenze else "tab:red" for j in js])
    ax2.axvline(grenze, color="black", ls="--")
    ax2.text(grenze + 0.5, max(probs) * 0.9, f"3^j = 2^k\nj = {grenze:.1f}", fontsize=9)
    ax2.set_xlabel(f"j = Anzahl ungerader Schritte unter k = {k}")
    ax2.set_ylabel("Anteil der Restklassen mod 2^k")
    ax2.set_title("Grün: nach k Schritten sicher kleiner")
    fig.tight_layout()
    if a.ausgabe:
        fig.savefig(a.ausgabe, dpi=120)
        print("Bild gespeichert:", a.ausgabe)
    else:
        plt.show()


if __name__ == "__main__":
    main()
