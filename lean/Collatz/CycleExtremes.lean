import Collatz.Counterexample

/-!
# Satz 71: Minimum und Maximum eines Zyklus

Für jeden Zyklus der beschleunigten Abbildung `T` (also `Titer p n = n` mit `p > 0`, `n > 0`),
den trivialen Zyklus `{1, 2}` eingeschlossen, gilt:

* Das **Maximum** `M` des Zyklus erfüllt `M ≡ 2 (mod 6)`. Sein Vorgänger `q` im Zyklus ist ungerade
  mit `q ≡ 1 (mod 4)` und `M = (3q+1)/2`.
* Das **Minimum** `m` des Zyklus ist ungerade, und sein Vorgänger im Zyklus ist genau `2m`.

Das ist eine allgemeine Strukturaussage über alle Zyklen, ohne Rechenschranke: Ein Zyklus muss
mit einem Abstieg `2m → m` in sein Minimum fallen und mit einem Aufstieg `q → (3q+1)/2` aus einem
Glied `q ≡ 1 (mod 4)` sein Maximum erreichen. Beides wird mit `ce_` präfixierten Hilfssätzen bewiesen.
-/

namespace Collatz

theorem ce_succ (i n : Nat) : Titer (i + 1) n = T (Titer i n) := by
  rw [Titer_add]; rfl

theorem ce_T_pos {n : Nat} (h : 0 < n) : 0 < T n := by
  unfold T; split <;> omega

theorem ce_pos {n : Nat} (h : 0 < n) : ∀ j, 0 < Titer j n := by
  intro j
  induction j with
  | zero => exact h
  | succ j ih => rw [ce_succ]; exact ce_T_pos ih

theorem ce_period {n p : Nat} (hc : Titer p n = n) : ∀ j, Titer j n = Titer (j % p) n := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases hj : j < p
    · rw [Nat.mod_eq_of_lt hj]
    · have hp : p ≤ j := Nat.le_of_not_lt hj
      have hp0 : 0 < p ∨ p = 0 := by omega
      rcases hp0 with hp0 | hp0
      · have e : j = p + (j - p) := by omega
        have h1 : Titer j n = Titer (j - p) n := by
          rw [e, Titer_add, hc]; congr 1; omega
        rw [h1, ih (j - p) (by omega)]
        congr 1
        conv => rhs; rw [e]
        rw [Nat.add_mod_left]
      · subst hp0; simp

theorem ce_argmax (f : Nat → Nat) : ∀ q, 0 < q → ∃ i, i < q ∧ ∀ j, j < q → f j ≤ f i := by
  intro q
  induction q with
  | zero => intro h; omega
  | succ q ih =>
    intro _
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq; exact ⟨0, by omega, fun j hj => by rw [show j = 0 by omega]; exact Nat.le_refl _⟩
    · obtain ⟨i, hi, hm⟩ := ih hq
      by_cases hle : f q ≤ f i
      · refine ⟨i, by omega, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · exact hm j hj
        · rw [hj]; exact hle
      · refine ⟨q, by omega, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · have := hm j hj; omega
        · rw [hj]; exact Nat.le_refl _

theorem ce_argmin (f : Nat → Nat) : ∀ q, 0 < q → ∃ i, i < q ∧ ∀ j, j < q → f i ≤ f j := by
  intro q
  induction q with
  | zero => intro h; omega
  | succ q ih =>
    intro _
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq; exact ⟨0, by omega, fun j hj => by rw [show j = 0 by omega]; exact Nat.le_refl _⟩
    · obtain ⟨i, hi, hm⟩ := ih hq
      by_cases hle : f i ≤ f q
      · refine ⟨i, by omega, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · exact hm j hj
        · rw [hj]; exact hle
      · refine ⟨q, by omega, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · have := hm j hj; omega
        · rw [hj]; exact Nat.le_refl _

/-- Vorgänger im Zyklus: `T (Titer (i+p-1) n) = Titer i n`. -/
theorem ce_pred {n p : Nat} (hp : 0 < p) (hc : Titer p n = n) (i : Nat) :
    T (Titer (i + p - 1) n) = Titer i n := by
  rw [← ce_succ, show i + p - 1 + 1 = p + i by omega, Titer_add, hc]

/-- **Satz 71a (Maximum eines Zyklus).** -/
theorem cycle_max_mod6 {n p : Nat} (hp : 0 < p) (h0 : 0 < n) (hc : Titer p n = n) :
    ∃ i, i < p ∧ (∀ j, Titer j n ≤ Titer i n) ∧ Titer i n % 6 = 2 ∧
      Titer (i + p - 1) n % 4 = 1 ∧ T (Titer (i + p - 1) n) = Titer i n := by
  obtain ⟨i, hi, hm⟩ := ce_argmax (fun j => Titer j n) p hp
  have hall : ∀ j, Titer j n ≤ Titer i n := by
    intro j; rw [ce_period hc j]; exact hm _ (Nat.mod_lt _ hp)
  have hy := ce_pred hp hc i
  have hyle := hall (i + p - 1)
  have hTx : T (Titer i n) ≤ Titer i n := by rw [← ce_succ]; exact hall (i + 1)
  have hx0 := ce_pos h0 i
  have hy0 := ce_pos h0 (i + p - 1)
  refine ⟨i, hi, hall, ?_, ?_, hy⟩
  · revert hy hyle hTx hx0 hy0
    generalize Titer i n = x
    generalize Titer (i + p - 1) n = y
    intro hy hyle hTx hx0 hy0
    unfold T at hy hTx
    split at hy <;> split at hTx <;> omega
  · revert hy hyle hTx hx0 hy0
    generalize Titer i n = x
    generalize Titer (i + p - 1) n = y
    intro hy hyle hTx hx0 hy0
    unfold T at hy hTx
    split at hy <;> split at hTx <;> omega

/-- **Satz 71b (Minimum eines Zyklus).** -/
theorem cycle_min_odd {n p : Nat} (hp : 0 < p) (h0 : 0 < n) (hc : Titer p n = n) :
    ∃ i, i < p ∧ (∀ j, Titer i n ≤ Titer j n) ∧ Titer i n % 2 = 1 ∧
      Titer (i + p - 1) n = 2 * Titer i n := by
  obtain ⟨i, hi, hm⟩ := ce_argmin (fun j => Titer j n) p hp
  have hall : ∀ j, Titer i n ≤ Titer j n := by
    intro j; rw [ce_period hc j]; exact hm _ (Nat.mod_lt _ hp)
  have hy := ce_pred hp hc i
  have hyle := hall (i + p - 1)
  have hTx : Titer i n ≤ T (Titer i n) := by rw [← ce_succ]; exact hall (i + 1)
  have hx0 := ce_pos h0 i
  refine ⟨i, hi, hall, ?_, ?_⟩
  · revert hy hyle hTx hx0
    generalize Titer i n = x
    generalize Titer (i + p - 1) n = y
    intro hy hyle hTx hx0
    unfold T at hy hTx
    split at hy <;> split at hTx <;> omega
  · revert hy hyle hTx hx0
    generalize Titer i n = x
    generalize Titer (i + p - 1) n = y
    intro hy hyle hTx hx0
    unfold T at hy hTx
    split at hy <;> split at hTx <;> omega

end Collatz
