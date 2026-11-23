import Collatz.CycleShape
import Collatz.Verified27All

/-!
# Form eines weiteren Zyklus mit der Schranke 2^27

Wie `CycleShape`, aber mit `m = 2^27`. Der obere Stern-Brocot-Nachbar ist jetzt
`23673/14936 > log₂(3 + 2^-27)`, und wieder ist `23673 · 665 − 1054 · 14936 = 1`.
-/

namespace Collatz

set_option exponentiation.threshold 400000 in
/-- Kernel-Rechnung: `(3 + 2^-27)^14936 < 2^23673`. -/
theorem upper_bound_27 : (3 * 134217728 + 1) ^ 14936 < 2 ^ 23673 * 134217728 ^ 14936 := by
  decide +kernel

/-- **Satz 27 (Form): Jeder weitere Zyklus hat `o = 665a + 14936b` ungerade und
`e = 1054a + 23673b` gerade Glieder, also die Länge `1719a + 38609b` mit `a, b ≥ 1`.** -/
theorem cycle_shape27 {n p : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ a b, 1 ≤ a ∧ 1 ≤ b ∧ oddCount n p = 665 * a + 14936 * b ∧
      evenCount n p = 1054 * a + 23673 * b ∧ p = 1719 * a + 38609 * b := by
  have hbig := nontrivial_cycle_ge_2_27 hp h0 hnt
  obtain ⟨ho, h3, hm⟩ := cycle_inequalities (m := 134217728) hp h0 hbig
  have hsum := odd_add_even n p
  have hu := ratio_upper ho hm upper_bound_27
  have hl := ratio_lower (by decide) h3 lower_bound_24
  generalize oddCount n p = o at *
  generalize evenCount n p = e at *
  refine ⟨23673 * o - 14936 * e, 665 * e - 1054 * o, by omega, by omega, by omega, by omega, by omega⟩

end Collatz
