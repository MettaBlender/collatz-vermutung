import Collatz.CycleShape
import Collatz.Verified25All

/-!
# Form eines weiteren Zyklus mit der Schranke 2^25

Wie `CycleShape`, aber mit `m = 2^25`. Der obere Stern-Brocot-Nachbar ist jetzt
`21565/13606 > log₂(3 + 2^-25)`, und wieder ist `21565 · 665 − 1054 · 13606 = 1`.
-/

namespace Collatz

set_option exponentiation.threshold 400000 in
/-- Kernel-Rechnung: `(3 + 2^-25)^13606 < 2^21565`. -/
theorem upper_bound_25 : (3 * 33554432 + 1) ^ 13606 < 2 ^ 21565 * 33554432 ^ 13606 := by
  decide +kernel

/-- **Satz 25 (Form): Jeder weitere Zyklus hat `o = 665a + 13606b` ungerade und
`e = 1054a + 21565b` gerade Glieder, also die Länge `1719a + 35171b` mit `a, b ≥ 1`.** -/
theorem cycle_shape25 {n p : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ a b, 1 ≤ a ∧ 1 ≤ b ∧ oddCount n p = 665 * a + 13606 * b ∧
      evenCount n p = 1054 * a + 21565 * b ∧ p = 1719 * a + 35171 * b := by
  have hbig := nontrivial_cycle_ge_2_25 hp h0 hnt
  obtain ⟨ho, h3, hm⟩ := cycle_inequalities (m := 33554432) hp h0 hbig
  have hsum := odd_add_even n p
  have hu := ratio_upper ho hm upper_bound_25
  have hl := ratio_lower (by decide) h3 lower_bound_24
  generalize oddCount n p = o at *
  generalize evenCount n p = e at *
  refine ⟨21565 * o - 13606 * e, 665 * e - 1054 * o, by omega, by omega, by omega, by omega, by omega⟩

end Collatz
