import Collatz.CycleShape
import Collatz.Verified26All

/-!
# Form eines weiteren Zyklus mit der Schranke 2^26

Wie `CycleShape`, aber mit `m = 2^26`. Der obere Stern-Brocot-Nachbar ist jetzt
`22619/14271 > log₂(3 + 2^-26)`, und wieder ist `22619 · 665 − 1054 · 14271 = 1`.
-/

namespace Collatz

set_option exponentiation.threshold 400000 in
/-- Kernel-Rechnung: `(3 + 2^-26)^14271 < 2^22619`. -/
theorem upper_bound_26 : (3 * 67108864 + 1) ^ 14271 < 2 ^ 22619 * 67108864 ^ 14271 := by
  decide +kernel

/-- **Satz 26 (Form): Jeder weitere Zyklus hat `o = 665a + 14271b` ungerade und
`e = 1054a + 22619b` gerade Glieder, also die Länge `1719a + 36890b` mit `a, b ≥ 1`.** -/
theorem cycle_shape26 {n p : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ a b, 1 ≤ a ∧ 1 ≤ b ∧ oddCount n p = 665 * a + 14271 * b ∧
      evenCount n p = 1054 * a + 22619 * b ∧ p = 1719 * a + 36890 * b := by
  have hbig := nontrivial_cycle_ge_2_26 hp h0 hnt
  obtain ⟨ho, h3, hm⟩ := cycle_inequalities (m := 67108864) hp h0 hbig
  have hsum := odd_add_even n p
  have hu := ratio_upper ho hm upper_bound_26
  have hl := ratio_lower (by decide) h3 lower_bound_24
  generalize oddCount n p = o at *
  generalize evenCount n p = e at *
  refine ⟨22619 * o - 14271 * e, 665 * e - 1054 * o, by omega, by omega, by omega, by omega, by omega⟩

end Collatz
