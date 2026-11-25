import Collatz.DoubleOdd

/-!
# Satz 63: Wachstum kostet Doppel-Aufstiege

Sei `doCnt n m j` die Zahl der Stellen `i ∈ [m, m+j)`, an denen zwei ungerade Schritte
direkt aufeinander folgen (Paritätsmuster `11`). Dann gilt für jede Bahn

  `x_{m+j} + 1 ≤ 2 · 4^(doCnt n m j) · (x_m + 1)`.

Jeder Faktor 4 an Wachstum muss also mit einem eigenen Doppel-Aufstieg bezahlt werden.
Insbesondere braucht eine Bahn, die von `x_m` auf `V` steigt, mindestens
`log₄((V+1) / (2(x_m+1)))` Doppel-Aufstiege. Satz 62 ist der Spezialfall `doCnt = 0`.
-/

namespace Collatz

/-- Anzahl der Muster `11` mit Startindex in `[m, m+j)`. -/
def doCnt (n m : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => doCnt n m j + (if nthPar (m + j) n = true ∧ nthPar (m + j + 1) n = true then 1 else 0)

theorem doCnt_mono (n m : Nat) {a b : Nat} (h : a ≤ b) : doCnt n m a ≤ doCnt n m b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | h'
    · have := ih (Nat.le_of_lt_succ h'); simp only [doCnt]; omega
    · subst h'; exact Nat.le_refl _

theorem doc_pow_mono (x : Nat) {a b : Nat} (h : a ≤ b) : 4 ^ a * (x + 1) ≤ 4 ^ b * (x + 1) :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) h)

theorem doc_par_true {i n : Nat} (h : Titer i n % 2 = 1) : nthPar i n = true := by
  unfold nthPar; simp [h]

/-- Invariante: entweder liegt `x+1` unter der aktuellen Schranke, oder der Vorgänger lag
unter seiner Schranke und war ungerade. -/
theorem doc_invariant (n m : Nat) :
    ∀ j, Titer (m + j) n + 1 ≤ 4 ^ doCnt n m j * (Titer m n + 1) ∨
      (∃ j', j = j' + 1 ∧ Titer (m + j') n + 1 ≤ 4 ^ doCnt n m j' * (Titer m n + 1) ∧
        Titer (m + j') n % 2 = 1) := by
  intro j
  induction j with
  | zero => left; simp [doCnt]
  | succ j ih =>
    rcases ih with hle | ⟨j', rfl, hz, hodd⟩
    · rcases Nat.mod_two_eq_zero_or_one (Titer (m + j) n) with he | ho
      · left
        have hm := doc_pow_mono (Titer m n) (doCnt_mono n m (show j ≤ j + 1 by omega))
        rw [← Nat.add_assoc, do_Titer_succ]
        unfold T; rw [if_pos he]
        have := Nat.div_le_self (Titer (m + j) n) 2
        omega
      · exact Or.inr ⟨j, rfl, hle, ho⟩
    · left
      have hy : Titer (m + j' + 1) n = (3 * Titer (m + j') n + 1) / 2 := by
        rw [do_Titer_succ]; unfold T; rw [if_neg (by omega)]
      have hm2 := doc_pow_mono (Titer m n) (doCnt_mono n m (show j' + 1 ≤ j' + 1 + 1 by omega))
      rw [show m + (j' + 1 + 1) = m + j' + 1 + 1 by omega, do_Titer_succ]
      rcases Nat.mod_two_eq_zero_or_one (Titer (m + j' + 1) n) with he | ho
      · have hm1 := doc_pow_mono (Titer m n) (doCnt_mono n m (show j' ≤ j' + 1 by omega))
        unfold T; rw [if_pos he, hy]
        omega
      · -- Doppel-Aufstieg an der Stelle m + j': er wird gezählt.
        have hc : doCnt n m (j' + 1) = doCnt n m j' + 1 := by
          simp only [doCnt]
          rw [if_pos ⟨doc_par_true hodd, doc_par_true ho⟩]
        have e : 4 ^ doCnt n m (j' + 1) * (Titer m n + 1)
            = 4 * (4 ^ doCnt n m j' * (Titer m n + 1)) := by
          rw [hc, Nat.pow_succ]; grind
        unfold T; rw [if_neg (by omega)]
        rw [hy] at ho ⊢
        generalize 4 ^ doCnt n m j' * (Titer m n + 1) = P at hz e
        omega

/-- **Satz 63.** Wachstum kostet Doppel-Aufstiege:
`x_{m+j} + 1 ≤ 2 · 4^(doCnt n m j) · (x_m + 1)`. -/
theorem double_odd_growth (n m j : Nat) :
    Titer (m + j) n + 1 ≤ 2 * (4 ^ doCnt n m j * (Titer m n + 1)) := by
  rcases doc_invariant n m j with hle | ⟨j', rfl, hz, hodd⟩
  · omega
  · have hm := doc_pow_mono (Titer m n) (doCnt_mono n m (show j' ≤ j' + 1 by omega))
    rw [← Nat.add_assoc, do_Titer_succ]; unfold T; rw [if_neg (by omega)]
    omega

/-- Folgerung: Steigt die Bahn über `2·4^k·(x_m+1)`, so gab es mehr als `k`
Doppel-Aufstiege. -/
theorem double_odd_count_lower {n m j k : Nat}
    (h : 2 * (4 ^ k * (Titer m n + 1)) < Titer (m + j) n + 1) : k < doCnt n m j := by
  apply Nat.lt_of_not_le
  intro hk
  have h1 := double_odd_growth n m j
  have h2 := doc_pow_mono (Titer m n) hk
  omega

/-- Für eine unbeschränkte Bahn wächst die Zahl der Doppel-Aufstiege über jede Schranke. -/
theorem unbounded_double_odd_count {n : Nat} (hu : ∀ B, ∃ i, B < Titer i n) (m k : Nat) :
    ∃ j, k < doCnt n m j := by
  obtain ⟨i, hi⟩ := hu (2 * (4 ^ k * (Titer m n + 1)) + ppSum n m)
  by_cases him : i < m
  · -- Werte vor m sind durch ppSum beschränkt
    have hS : ∀ k r, r < k → Titer r n ≤ ppSum n k := by
      intro k
      induction k with
      | zero => intro r hr; omega
      | succ k ih =>
        intro r hr
        show Titer r n ≤ ppSum n k + Titer k n
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h' | h'
        · have := ih r h'; omega
        · subst h'; omega
    have := hS m i him; omega
  · refine ⟨i - m, double_odd_count_lower ?_⟩
    rw [show m + (i - m) = i by omega]; omega

end Collatz
