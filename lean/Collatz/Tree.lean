import Collatz.Basic

/-!
# Der Collatz-Baum: Vorgänger

Rückwärts betrachtet hat jede Zahl `n` den Vorgänger `2n` und eventuell einen
ungeraden Vorgänger `(n-1)/3`. Hier beweisen wir die Fakten, die im Python-Experiment
(`python/baum.py`, `python/collatz_verteilung.py`) auffallen.
-/

namespace Collatz

/-- **Vorgänger-Charakterisierung**: `step m = n` genau dann, wenn `m = 2n` ist oder
`m` ungerade mit `3m + 1 = n`. -/
theorem step_eq_iff (m n : Nat) :
    step m = n ↔ m = 2 * n ∨ (m % 2 = 1 ∧ 3 * m + 1 = n) := by
  unfold step
  split <;> omega

/-- `3m + 1` ist nie durch 3 teilbar. -/
theorem three_mul_add_one_mod_three (m : Nat) : (3 * m + 1) % 3 = 1 := by omega

/-- **Vielfache von 3 haben nur den Vorgänger `2n`**: Deshalb werden sie im
Verteilungs-Diagramm so selten besucht. -/
theorem pred_of_mul_three {m n : Nat} (h3 : n % 3 = 0) (h : step m = n) : m = 2 * n := by
  rw [step_eq_iff] at h
  omega

/-- Einen ungeraden Vorgänger gibt es genau für `n ≡ 4 (mod 6)`. -/
theorem odd_pred_iff (n : Nat) :
    (∃ m, m % 2 = 1 ∧ step m = n) ↔ n % 6 = 4 := by
  constructor
  · rintro ⟨m, hm, h⟩
    rw [step_eq_iff] at h
    omega
  · intro h
    refine ⟨(n - 1) / 3, by omega, ?_⟩
    rw [step_eq_iff]; omega

/-- **Die 8 hat nur den Vorgänger 16**, die 4 nur 8 und 1. Darum läuft jede Folge
(ausser ab 1, 2, 4, 8) über 16 → 8 → 4 → 2 → 1. -/
theorem pred_eight {m : Nat} (h : step m = 8) : m = 16 := by
  rw [step_eq_iff] at h; omega

theorem pred_four {m : Nat} (h : step m = 4) : m = 8 ∨ m = 1 := by
  rw [step_eq_iff] at h; omega

theorem pred_two {m : Nat} (h : step m = 2) : m = 4 := by
  rw [step_eq_iff] at h; omega

theorem pred_sixteen {m : Nat} (h : step m = 16) : m = 32 ∨ m = 5 := by
  rw [step_eq_iff] at h; omega

/-- Jede Folge, die die 1 erreicht und nicht bei 1, 2, 4, 8 oder 16 startet,
kommt durch die 16. -/
theorem passes_sixteen {n k : Nat} (hk : iter k n = 1)
    (hn : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4 ∧ n ≠ 8 ∧ n ≠ 16) : ∃ j, iter j n = 16 := by
  -- Rückwärts: der letzte Schritt vor 1 kommt von 2 (oder die Folge war schon bei 1),
  -- davor 4, davor 8, davor 16.
  induction k generalizing n with
  | zero => simp at hk; omega
  | succ k ih =>
    rw [iter_succ] at hk
    by_cases hs : step n = 1 ∨ step n = 2 ∨ step n = 4 ∨ step n = 8 ∨ step n = 16
    · rcases hs with h | h | h | h | h
      · rw [step_eq_iff] at h; omega
      · exact absurd (pred_two h) hn.2.2.1
      · rcases pred_four h with h' | h' <;> omega
      · exact absurd (pred_eight h) hn.2.2.2.2
      · exact ⟨1, h⟩
    · obtain ⟨j, hj⟩ := ih hk (by omega)
      exact ⟨j + 1, hj⟩

end Collatz
