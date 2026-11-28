import Mathlib

/-!
# Satz 87: log₂ 3 ist irrational, und jeder Zyklus hat L/O > log₂ 3

Erster Satz mit Mathlib. Für einen Collatz-Zyklus mit `O` ungeraden Schritten und
`L` Schritten insgesamt gilt `3^O < 2^L` (Produktformel, Satz 77). Hier zeigen wir:

* `logb_two_three_irrational`: `log₂ 3` ist keine rationale Zahl `p/q`.
* `cycle_ratio_gt_logb`: aus `3^O < 2^L` mit `O ≥ 1` folgt `log₂ 3 < L / O`.

Zusammen: Das Verhältnis `L/O` eines Zyklus liegt *echt* über der irrationalen
Zahl `log₂ 3 ≈ 1.585`. Wie nahe es herankommen kann, ist genau die Frage nach
rationalen Näherungen von `log₂ 3`, die Baker-Theorie quantitativ beantwortet
(Baker selbst ist nicht in Mathlib formalisiert).
-/

namespace CollatzM

open Real

theorem two_pow_ne_three_pow (p q : ℕ) (hq : 1 ≤ q) : 2 ^ p ≠ 3 ^ q := by
  intro h
  have h3 : (3 ^ q) % 2 = 1 := by
    rw [Nat.pow_mod]; norm_num
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    have : 3 ≤ 3 ^ q := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ q := Nat.pow_le_pow_right (by norm_num) hq
    omega
  · have h2 : (2 ^ p) % 2 = 0 := by
      obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
      rw [pow_succ]; simp
    omega

theorem logb_two_three_irrational (p q : ℕ) (hq : 1 ≤ q) :
    Real.logb 2 3 ≠ (p : ℝ) / q := by
  intro h
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog : Real.log 3 * q = Real.log 2 * p := by
    have := h
    rw [Real.logb, div_eq_div_iff (Real.log_pos (by norm_num)).ne' hq'.ne'] at this
    linarith
  have hpow : ((3 : ℝ) ^ q) = (2 : ℝ) ^ p := by
    have e1 : Real.log ((3 : ℝ) ^ q) = Real.log ((2 : ℝ) ^ p) := by
      rw [Real.log_pow, Real.log_pow]; linarith
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (by positivity)) e1
  have hnat : (3 : ℕ) ^ q = 2 ^ p := by exact_mod_cast hpow
  exact two_pow_ne_three_pow p q hq hnat.symm

theorem cycle_ratio_gt_logb (O L : ℕ) (hO : 1 ≤ O) (h : 3 ^ O < 2 ^ L) :
    Real.logb 2 3 < (L : ℝ) / O := by
  have hO' : (0 : ℝ) < O := by exact_mod_cast hO
  have hr : ((3 : ℝ) ^ O) < (2 : ℝ) ^ L := by exact_mod_cast h
  have hl : Real.log ((3 : ℝ) ^ O) < Real.log ((2 : ℝ) ^ L) :=
    Real.log_lt_log (by positivity) hr
  rw [Real.log_pow, Real.log_pow] at hl
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.logb, div_lt_div_iff₀ h2 hO']
  linarith

end CollatzM
