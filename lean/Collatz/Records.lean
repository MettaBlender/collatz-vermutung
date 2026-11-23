import Collatz.Basic

/-!
# Rekorde einer Collatz-Folge

Ein **Rekord** der Folge `n, step n, step² n, …` ist ein Glied `iter k n` mit `k > 0`, das
grösser ist als alle früheren Glieder. Für **alle** natürlichen Zahlen gilt:

* `record_form`: Jeder Rekord entsteht aus einem ungeraden Vorgänger `x` als `3x + 1` und ist
  daher `≡ 4 (mod 6)`. (Ein Halbierungsschritt verkleinert, kann also keinen Rekord liefern.)
* `records_of_unbounded`: Ist die Folge unbeschränkt, so gibt es Rekorde über jeder Schranke.
* **Satz** (`divergent_records`): Eine divergente Folge hat unendlich viele Rekorde, und jeder
  davon ist von der Form `3x + 1` mit `x` ungerade, also `≡ 4 (mod 6)`.

Das ist ein kleiner, aber struktureller Baustein: Ein Divergenz-Beweis müsste zeigen, dass
diese Rekordkette nicht beliebig lange weitergeht.
-/

namespace Collatz

/-- **Form eines Rekords.** -/
theorem record_form (n k : Nat) (hk : 0 < k) (hrec : ∀ i < k, iter i n < iter k n) :
    ∃ x, x % 2 = 1 ∧ iter (k - 1) n = x ∧ iter k n = 3 * x + 1 ∧ iter k n % 6 = 4 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hlt := hrec j (by omega)
  rw [iter_succ'] at hlt ⊢
  refine ⟨iter j n, ?_, by simp, ?_⟩
  · rcases Nat.mod_two_eq_zero_or_one (iter j n) with h | h
    · rw [step_even h] at hlt; omega
    · exact h
  · have hodd : iter j n % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (iter j n) with h | h
      · rw [step_even h] at hlt; omega
      · exact h
    rw [step_odd hodd]; refine ⟨rfl, ?_⟩; omega

/-- Kleinster Index, an dem eine Eigenschaft gilt (ohne `Nat.find`). -/
theorem exists_min_index (P : Nat → Prop) :
    ∀ k, P k → ∃ m, m ≤ k ∧ P m ∧ ∀ i < m, ¬ P i := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    by_cases h : ∃ i < k, P i
    · obtain ⟨i, hi, hPi⟩ := h
      obtain ⟨m, hm, hPm, hmin⟩ := ih i hi hPi
      exact ⟨m, by omega, hPm, hmin⟩
    · exact ⟨k, Nat.le_refl k, hk, fun i hi hPi => h ⟨i, hi, hPi⟩⟩

/-- **Rekorde über jeder Schranke.** -/
theorem records_of_unbounded (n : Nat) (h : ∀ B, ∃ k, B < iter k n) (B : Nat) :
    ∃ k, 0 < k ∧ B < iter k n ∧ ∀ i < k, iter i n < iter k n := by
  obtain ⟨k, hk⟩ := h (max B n)
  obtain ⟨m, -, hPm, hmin⟩ := exists_min_index (fun k => max B n < iter k n) k hk
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp [iter] at hPm; omega
    · exact h0
  refine ⟨m, hm, by omega, fun i hi => ?_⟩
  have := hmin i hi
  omega

/-- **Satz.** Eine divergente Folge hat Rekorde über jeder Schranke, und jeder Rekord ist `3x + 1`
für ein ungerades `x`, also `≡ 4 (mod 6)`. -/
theorem divergent_records (n : Nat) (h : ∀ B, ∃ k, B < iter k n) (B : Nat) :
    ∃ k x, 0 < k ∧ B < iter k n ∧ (∀ i < k, iter i n < iter k n) ∧
      x % 2 = 1 ∧ iter (k - 1) n = x ∧ iter k n = 3 * x + 1 ∧ iter k n % 6 = 4 := by
  obtain ⟨k, hk, hB, hrec⟩ := records_of_unbounded n h B
  obtain ⟨x, hx, h1, h2, h3⟩ := record_form n k hk hrec
  exact ⟨k, x, hk, hB, hrec, hx, h1, h2, h3⟩

end Collatz
