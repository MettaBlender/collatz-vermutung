"""Der gewichtete Crandall-Baum: Exponent 0.291 statt 0.224 (Lean: Weighted.lean, Satz 45).

Im Baum aus crandall.py ist nur das Kind child(n, True) bis 22n gross; das andere Kind
child(n, False) ist kleiner als 6n. Ein Weg der Länge t mit a kleinen Schritten endet bei einer
Zahl <= 5 · 6^a · 22^(t-a), und genau C(t, a) Wege haben a kleine Schritte. Optimiert man a,
so erreichen für jedes x etwa x^α Zahlen <= x die 1, mit 6^(-α) + 22^(-α) = 1, α ≈ 0.2912.

    python gewichteter_baum.py
"""

from __future__ import annotations

from math import comb, log

from crandall import child, erreicht_eins, node


def zeros(t: int, k: int) -> int:
    """Anzahl kleiner Schritte (Bit 0) auf dem Weg k der Länge t, wie in Lean."""
    return sum(1 for i in range(t) if (k >> i) & 1 == 0)


def alpha(eps: float = 1e-12) -> float:
    """Löst 6^(-α) + 22^(-α) = 1 per Bisektion."""
    lo, hi = 0.0, 1.0
    while hi - lo > eps:
        mid = (lo + hi) / 2
        if 6 ** -mid + 22 ** -mid > 1:
            lo = mid
        else:
            hi = mid
    return lo


def pruefe(t: int) -> bool:
    """Prüft für Tiefe t: Schranke, Zählung C(t, a), Verschiedenheit, alle erreichen 1."""
    werte = [node(t, k) for k in range(2 ** t)]
    if len(set(werte)) != len(werte):
        return False
    for a in range(t + 1):
        wege = [k for k in range(2 ** t) if zeros(t, k) == a]
        if len(wege) != comb(t, a):
            return False
        if any(node(t, k) > 5 * 6 ** a * 22 ** (t - a) for k in wege):
            return False
    return all(erreicht_eins(n) for n in werte)


def main() -> None:
    print("Kleines Kind < 6n:", all(child(n, False) < 6 * n for n in range(1, 10 ** 5, 2) if n % 3))
    for t in range(1, 13):
        print(f"t = {t:2d}: Schranke, Zählung und Verschiedenheit stimmen: {pruefe(t)}")
    a = alpha()
    print(f"\nExponent: α mit 6^-α + 22^-α = 1 ist {a:.4f} (vorher log 2/log 22 = {log(2) / log(22):.4f})")
    t = 60
    best = max(range(t + 1), key=lambda j: log(comb(t, j)) / log(5 * 6 ** j * 22 ** (t - j)))
    x = 5 * 6 ** best * 22 ** (t - best)
    print(f"Beispiel t = {t}, a = {best}: C(t,a) = {comb(t, best):.3e} Zahlen <= {x:.3e},"
          f" also x^{log(comb(t, best)) / log(x):.3f}")


if __name__ == "__main__":
    main()
