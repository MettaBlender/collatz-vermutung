"""Prüft die Collatz-Vermutung für alle Startzahlen bis N.

Es genügt zu prüfen, dass jede Zahl n > 1 irgendwann unter n fällt (siehe Lean-Satz
`conjecture_of_descends`): dann erreichen per Induktion alle Zahlen die 1.
Zusätzlich werden gerade Zahlen und n ≡ 1 (mod 4) übersprungen, weil sie
bewiesenermassen abfallen (Lean: `descends_of_even`, `descends_of_mod_four_eq_one`).

    python verifizieren.py 10000000
"""

from __future__ import annotations

import argparse
import time


def pruefe(bis: int) -> tuple[int, int, int]:
    """Gibt (geprüfte Zahlen, längste Stoppzeit, Startzahl dazu) zurück."""
    geprueft, best, best_n = 0, 0, 0
    for n in range(3, bis + 1, 4):  # nur n ≡ 3 (mod 4)
        x, k = n, 0
        while x >= n:
            x = x // 2 if x % 2 == 0 else 3 * x + 1
            k += 1
        geprueft += 1
        if k > best:
            best, best_n = k, n
    return geprueft, best, best_n


def main(argv: list[str] | None = None) -> None:
    p = argparse.ArgumentParser(description="Verifikation bis N")
    p.add_argument("bis", type=int, nargs="?", default=1_000_000)
    a = p.parse_args(argv)
    t0 = time.time()
    geprueft, best, best_n = pruefe(a.bis)
    print(f"Alle Zahlen 1..{a.bis} erreichen die 1. "
          f"({geprueft} Zahlen n ≡ 3 mod 4 explizit geprüft, {time.time() - t0:.1f} s)")
    print(f"Längste Stoppzeit σ(n) dabei: {best} Schritte bei n = {best_n}")


if __name__ == "__main__":
    main()
