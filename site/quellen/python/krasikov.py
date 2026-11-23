"""Rückwärtsbaum mit Buchführung modulo 3^J (Methode von Krasikov; Lean: Krasikov.lean, Satz 47).

Ein ungerader Vorfahre von n ist c = (2^E·n − 1)/3, falls 2^E·n ≡ 1 (mod 3); er ist nicht durch 3
teilbar, falls 2^E·n ≢ 1 (mod 9), und c < 2^E·n/3. Die Klasse von c modulo 3^(J−1) hängt nur von
n mod 3^J und E ab. Weil man die Klasse von c modulo 3^J nicht kennt, nimmt man das Minimum über die
drei Hebungen. Die Tabelle q[d][t][S] ist eine bewiesene untere Schranke: Unter jedem n ≡ t
(mod 3^(J−1)) liegen mindestens q[d][t][S] verschiedene Zahlen m in Tiefe d mit 3^d·m ≤ 2^S·n.

Ein Block (d0, S0) mit L0 = min_t q[d0][t][S0] lässt sich k-mal aneinanderhängen: L0^k Zahlen
≤ n·(2^S0/3^d0)^k. Exponent log L0 / log(2^S0/3^d0).

    python krasikov.py
"""

from __future__ import annotations

from math import log


def tabelle(J: int, Emax: int, Smax: int, D: int) -> list[dict[int, list[int]]]:
    M, Mt = 3 ** J, 3 ** (J - 1)

    def kind(s: int, E: int) -> int | None:
        v = (pow(2, E, M) * s) % M
        if v % 3 != 1:
            return None
        c = (v - 1) // 3
        return None if c % 3 == 0 else c

    kinder = {s: [(E, kind(s, E)) for E in range(1, Emax + 1) if kind(s, E) is not None]
              for s in range(M) if s % 3}
    typen = [t for t in range(Mt) if t % 3]
    q = {t: [1] * (Smax + 1) for t in typen}
    tabs = [q]
    for _ in range(D):
        q = {t: [min(sum(q[c][S - E] for E, c in kinder[s] if E <= S) for s in (t, t + Mt, t + 2 * Mt))
                 for S in range(Smax + 1)] for t in typen}
        tabs.append(q)
    return tabs


def exponent(J: int, Emax: int, d0: int, S0: int) -> tuple[int, float]:
    q = tabelle(J, Emax, S0, d0)[d0]
    L0 = min(row[S0] for row in q.values())
    return L0, log(L0) / (S0 * log(2) - d0 * log(3))


def baum_zaehlen(n: int, d: int, S: int, J: int, Emax: int) -> int:
    """Zählt die Knoten in Tiefe d unter n mit 3^d·m <= 2^S·n direkt (nur kleine Werte)."""
    if d == 0:
        return 1
    total = 0
    for E in range(1, min(S, Emax) + 1):
        v = 2 ** E * n
        if v % 3 == 1 and v % 9 != 1:
            total += baum_zaehlen((v - 1) // 3, d - 1, S - E, J, Emax)
    return total


def main() -> None:
    L0, a = exponent(4, 10, 14, 50)
    print(f"Block J=4, Emax=10, d0=14, S0=50 (in Lean): L0 = {L0}, Exponent {a:.4f}")
    L1, b = exponent(4, 10, 20, 70)
    print(f"Grösserer Block d0=20, S0=70: L0 = {L1}, Exponent {b:.4f}")
    q = tabelle(3, 10, 30, 4)
    ok = all(baum_zaehlen(n, 4, 30, 3, 10) >= q[4][n % 9][30] for n in range(1, 400, 2) if n % 3)
    print("Tabelle ist untere Schranke für den echten Baum (n < 400, Tiefe 4):", ok)
    print("Grenzwerte der Methode (alle E, Tiefe gegen unendlich):",
          "J=2: 0.437, J=3: 0.611, J=4: 0.689, J=5: 0.734, J=6: 0.761, J=7: 0.783")


if __name__ == "__main__":
    main()
