import Collatz.CycleLength

/-!
# Schnellere Kernel-Prüfung der Zyklus-Ungleichung

`noShortCycle` rechnet für jedes `j` die Potenzen neu aus und braucht `log₂`. Hier laufen
`P = (3m+1)^j`, `Q = m^j`, `T = 3^j` und `E = 2^e` (mit `T < E ≤ 2T`, also `e` minimal mit
`3^j < 2^e`) mit, und jeder Schritt multipliziert nur mit kleinen Zahlen.
-/

namespace Collatz

/-- Prüft `(3m+1)^i < 2^e · m^i` für die nächsten `fuel` Exponenten `i`, mit dem kleinsten `e`,
für das `3^i < 2^e` gilt. -/
def cycleCheck (m : Nat) : (fuel P Q T E : Nat) → Bool
  | 0, _, _, _, _ => true
  | f + 1, P, Q, T, E =>
    let E' := if 3 * T < 2 * E then 2 * E else 4 * E
    decide ((3 * m + 1) * P < E' * (m * Q)) && cycleCheck m f ((3 * m + 1) * P) (m * Q) (3 * T) E'

private theorem pow_le_of_lt_two_mul {a b : Nat} (h : 2 ^ a < 2 * 2 ^ b) : 2 ^ a ≤ 2 ^ b := by
  have h' : 2 ^ a < 2 ^ (b + 1) := by rw [Nat.pow_succ, Nat.mul_comm]; exact h
  have hab : a < b + 1 := (Nat.pow_lt_pow_iff_right (by decide)).mp h'
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem cycleCheck_spec (m : Nat) : ∀ f j P Q T e,
    P = (3 * m + 1) ^ j → Q = m ^ j → T = 3 ^ j → T < 2 ^ e → 2 ^ e ≤ 2 * T →
    cycleCheck m f P Q T (2 ^ e) = true →
    ∀ i, j < i → i ≤ j + f → ∀ e₂, 3 ^ i < 2 ^ e₂ → (3 * m + 1) ^ i < 2 ^ e₂ * m ^ i := by
  intro f
  induction f with
  | zero => intro j P Q T e _ _ _ _ _ _ i h1 h2; omega
  | succ f ih =>
    intro j P Q T e hP hQ hT hlo hhi h i hi1 hi2 e₂ he₂
    unfold cycleCheck at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hnow, hrest⟩ := h
    -- neues e' mit E' = 2^e'
    obtain ⟨e', hE', hlo', hhi'⟩ : ∃ e', (if 3 * T < 2 * 2 ^ e then 2 * 2 ^ e else 4 * 2 ^ e) = 2 ^ e' ∧
        3 * T < 2 ^ e' ∧ 2 ^ e' ≤ 2 * (3 * T) := by
      by_cases hc : 3 * T < 2 * 2 ^ e
      · refine ⟨e + 1, by rw [if_pos hc, Nat.pow_succ, Nat.mul_comm], ?_, ?_⟩ <;>
          rw [Nat.pow_succ] <;> omega
      · refine ⟨e + 2, by rw [if_neg hc, Nat.pow_add, Nat.mul_comm], ?_, ?_⟩ <;>
          rw [Nat.pow_add, show (2:Nat) ^ 2 = 4 from rfl] <;> omega
    rw [hE'] at hnow hrest
    have hP' : (3 * m + 1) * P = (3 * m + 1) ^ (j + 1) := by rw [hP, Nat.pow_succ, Nat.mul_comm]
    have hQ' : m * Q = m ^ (j + 1) := by rw [hQ, Nat.pow_succ, Nat.mul_comm]
    have hT' : 3 * T = 3 ^ (j + 1) := by rw [hT, Nat.pow_succ, Nat.mul_comm]
    by_cases hij : i = j + 1
    · subst hij
      rw [hP', hQ'] at hnow
      -- 2^e' ≤ 2·3^i < 2·2^e₂, also 2^e' ≤ 2^e₂
      have hle : 2 ^ e' ≤ 2 ^ e₂ := pow_le_of_lt_two_mul (by rw [← hT'] at he₂; omega)
      have := Nat.mul_le_mul_right (m ^ (j + 1)) hle
      omega
    · exact ih (j + 1) _ _ _ e' hP' hQ' hT' hlo' hhi' hrest i (by omega) (by omega) e₂ he₂

/-- Startwerte `j = 0`: `P = Q = T = 1`, `E = 2`. -/
theorem cycleCheck_start {m J : Nat} (h : cycleCheck m J 1 1 1 2 = true) :
    ∀ i, 0 < i → i ≤ J → ∀ e₂, 3 ^ i < 2 ^ e₂ → (3 * m + 1) ^ i < 2 ^ e₂ * m ^ i :=
  fun i h1 h2 => cycleCheck_spec m J 0 1 1 1 1 (by simp) (by simp) (by simp) (by decide) (by decide)
    h i h1 (by omega)

/-- **Allgemeine Schranke**: Liegen alle Glieder eines Zyklus bei mindestens `m` und besteht
`cycleCheck m J 1 1 1 2`, so hat der Zyklus mehr als `J` ungerade Glieder. -/
theorem cycle_odd_gt {n p m J : Nat} (hp : Periodic n p) (h0 : 0 < n) (hm : ∀ i, m ≤ iter i n)
    (hc : cycleCheck m J 1 1 1 2 = true) : J < oddCount n p := by
  obtain ⟨hj, h3, h2⟩ := cycle_inequalities hp h0 hm
  apply Nat.lt_of_not_le
  intro hle
  have := cycleCheck_start hc (oddCount n p) hj hle (evenCount n p) h3
  omega

end Collatz
