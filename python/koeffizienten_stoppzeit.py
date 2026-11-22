"""Terras' Koeffizienten-Stoppzeit-Vermutung nachrechnen.

Für T(n) = n/2 bzw. (3n+1)/2 ist die Stoppzeit σ(n) der erste Schritt j >= 1 mit
T^j(n) < n, und die Koeffizienten-Stoppzeit τ(n) der erste Schritt j mit 3^o < 2^j
(o = Zahl der ungeraden unter den ersten j Schritten).

Immer gilt τ(n) <= σ(n) (in Lean: CoeffStopping.lean, coeff_of_descent). Terras vermutete
σ(n) = τ(n) für alle n >= 2; das ist offen. Würde es gelten, gäbe es keine weiteren Zyklen
(Lean: no_cycle_of_coeffStopping). Dieses Skript prüft die Gleichheit für alle n < N.

    python koeffizienten_stoppzeit.py [N]
"""

from __future__ import annotations

import sys


def stoppzeiten(n: int) -> tuple[int, int]:
    """(σ(n), τ(n)) für n >= 2."""
    x, j, o, p3, p2 = n, 0, 0, 1, 1
    tau = None
    while True:
        if x % 2:
            x = (3 * x + 1) // 2
            o += 1
            p3 *= 3
        else:
            x //= 2
        j += 1
        p2 *= 2
        if tau is None and p3 < p2:
            tau = j
        if x < n:
            return j, tau


def pruefe(N: int) -> tuple[int, int]:
    """Gibt (Anzahl Abweichungen, grösste Stoppzeit) für 2 <= n < N zurück."""
    abweichungen, maximum = 0, 0
    for n in range(2, N):
        s, t = stoppzeiten(n)
        if s != t:
            abweichungen += 1
        maximum = max(maximum, s)
    return abweichungen, maximum


def main(argv: list[str] | None = None) -> None:
    argv = sys.argv[1:] if argv is None else argv
    N = int(argv[0]) if argv else 10**7
    abw, mx = pruefe(N)
    print(f"2 <= n < {N:,}: σ(n) = τ(n) bei allen ausser {abw} Zahlen; grösste Stoppzeit {mx}".replace(",", "'"))


if __name__ == "__main__":
    main()
