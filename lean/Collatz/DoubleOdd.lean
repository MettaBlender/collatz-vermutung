import Collatz.PeriodicParity

/-!
# Satz 62: Divergente Bahnen enthalten unendlich oft zwei ungerade Schritte hintereinander

Folgt in der Bahn von `n` ab Index `m` nie auf einen ungeraden Schritt ein weiterer
ungerader Schritt, so bleibt die Bahn durch `2·x_m + 1` beschränkt: Nach jedem
Aufstieg `x ↦ (3x+1)/2` folgt zwingend ein Halbieren auf `(3x+1)/4 ≤ x`.
Kontraposition: eine unbeschränkte Bahn enthält unendlich oft das Paritätsmuster `11`.
-/

namespace Collatz

theorem do_Titer_succ (k n : Nat) : Titer (k + 1) n = T (Titer k n) := by
  rw [pp_Titer_add]; rfl

/-- Invariante: entweder liegt der Wert unter `X`, oder der Vorgänger lag unter `X`
und war ungerade. -/
theorem do_invariant {n m : Nat}
    (h : ∀ i, m ≤ i → ¬ (nthPar i n = true ∧ nthPar (i + 1) n = true)) :
    ∀ j, Titer (m + j) n ≤ Titer m n ∨
      (∃ j', j = j' + 1 ∧ Titer (m + j') n ≤ Titer m n ∧ Titer (m + j') n % 2 = 1) := by
  intro j
  induction j with
  | zero => exact Or.inl (Nat.le_refl _)
  | succ j ih =>
    rcases ih with hle | ⟨j', rfl, hz, hodd⟩
    · rcases Nat.mod_two_eq_zero_or_one (Titer (m + j) n) with he | ho
      · left
        rw [← Nat.add_assoc, do_Titer_succ]
        unfold T; rw [if_pos he]
        exact Nat.le_trans (Nat.div_le_self _ _) hle
      · exact Or.inr ⟨j, rfl, hle, ho⟩
    · left
      have hnp := h (m + j') (Nat.le_add_right _ _)
      have h1 : nthPar (m + j') n = true := by
        unfold nthPar; simp [hodd]
      have h2 : nthPar (m + j' + 1) n = false := by
        cases hb : nthPar (m + j' + 1) n
        · rfl
        · exact absurd ⟨h1, hb⟩ hnp
      have hy : Titer (m + j' + 1) n = (3 * Titer (m + j') n + 1) / 2 := by
        rw [do_Titer_succ]; unfold T; rw [if_neg (by omega)]
      have hye : Titer (m + j' + 1) n % 2 = 0 := by
        unfold nthPar at h2; simp at h2; omega
      rw [show m + (j' + 1 + 1) = m + j' + 1 + 1 by omega, do_Titer_succ]
      unfold T; rw [if_pos hye, hy]
      omega

/-- Ohne das Muster `11` ab Index `m` ist die Bahn durch `2·x_m + 1` beschränkt. -/
theorem no_double_odd_bounded {n m : Nat}
    (h : ∀ i, m ≤ i → ¬ (nthPar i n = true ∧ nthPar (i + 1) n = true)) :
    ∀ j, Titer (m + j) n ≤ 2 * Titer m n + 1 := by
  intro j
  rcases do_invariant h j with hle | ⟨j', rfl, hz, hodd⟩
  · omega
  · rw [← Nat.add_assoc, do_Titer_succ]; unfold T; rw [if_neg (by omega)]; omega

/-- **Satz 62.** Eine unbeschränkte Bahn enthält ab jedem Index noch einmal zwei
ungerade Schritte direkt hintereinander. -/
theorem unbounded_double_odd {n : Nat} (hu : ∀ B, ∃ i, B < Titer i n) (m : Nat) :
    ∃ i, m ≤ i ∧ nthPar i n = true ∧ nthPar (i + 1) n = true := by
  apply Classical.byContradiction
  intro hne
  have h : ∀ i, m ≤ i → ¬ (nthPar i n = true ∧ nthPar (i + 1) n = true) :=
    fun i hi hp => hne ⟨i, hi, hp⟩
  have hb := no_double_odd_bounded h
  -- Werte vor `m` sind durch ihre Summe beschränkt.
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
  obtain ⟨i, hi⟩ := hu (ppSum n m + 2 * Titer m n + 1)
  by_cases him : i < m
  · have := hS m i him; omega
  · have := hb (i - m)
    rw [show m + (i - m) = i by omega] at this
    omega

end Collatz
