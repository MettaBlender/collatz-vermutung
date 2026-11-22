import Collatz.Cycles

/-!
# Die zwei Arten von Gegenbeispielen

Die Collatz-Vermutung ist **genau dann** wahr, wenn

1. jede Folge beschränkt bleibt (keine Folge wächst über alle Grenzen), und
2. jeder Zyklus der triviale Zyklus `1 → 4 → 2 → 1` ist.

Die Richtung „⇐“ benutzt das Schubfachprinzip: Eine beschränkte Folge muss einen Wert
wiederholen und läuft danach in einen Zyklus.
-/

namespace Collatz

/-- **Schubfachprinzip**: `B + 2` Werte aus `{0, …, B}` enthalten zwei gleiche. -/
theorem pigeonhole (B : Nat) :
    ∀ f : Nat → Nat, (∀ i, i ≤ B + 1 → f i ≤ B) → ∃ i j, i < j ∧ j ≤ B + 1 ∧ f i = f j := by
  induction B with
  | zero =>
    intro f hf
    exact ⟨0, 1, by omega, by omega, by have := hf 0 (by omega); have := hf 1 (by omega); omega⟩
  | succ B ih =>
    intro f hf
    by_cases h : ∃ i, i ≤ B + 1 ∧ f i = f (B + 2)
    · obtain ⟨i, hi, he⟩ := h
      exact ⟨i, B + 2, by omega, by omega, he⟩
    · have hne : ∀ i, i ≤ B + 1 → f i ≠ f (B + 2) := fun i hi he => h ⟨i, hi, he⟩
      -- Den Wert f (B+2) herausnehmen und die grösseren Werte um 1 nach unten schieben.
      let g : Nat → Nat := fun i => if f (B + 2) < f i then f i - 1 else f i
      have hg : ∀ i, i ≤ B + 1 → g i ≤ B := by
        intro i hi
        have h1 := hf i (by omega)
        have h2 := hf (B + 2) (by omega)
        have h3 := hne i hi
        simp only [g]; split <;> omega
      obtain ⟨i, j, hij, hj, he⟩ := ih g hg
      refine ⟨i, j, hij, by omega, ?_⟩
      have hi' := hne i (by omega)
      have hj' := hne j hj
      simp only [g] at he
      split at he <;> split at he <;> omega

/-- **Eine beschränkte Folge läuft in einen Zyklus.** -/
theorem eventually_periodic {n B : Nat} (hB : ∀ k, iter k n ≤ B) :
    ∃ k p, Periodic (iter k n) p := by
  obtain ⟨i, j, hij, -, he⟩ := pigeonhole B (fun k => iter k n) (fun k _ => hB k)
  refine ⟨i, j - i, by omega, ?_⟩
  rw [← iter_add, Nat.add_sub_cancel' (Nat.le_of_lt hij)]
  exact he.symm

/-- Das Maximum der ersten `m + 1` Folgenglieder. -/
def maxUpTo (n : Nat) : Nat → Nat
  | 0 => n
  | m + 1 => max (maxUpTo n m) (iter (m + 1) n)

theorem iter_le_maxUpTo (n : Nat) : ∀ m k, k ≤ m → iter k n ≤ maxUpTo n m := by
  intro m
  induction m with
  | zero => intro k hk; have : k = 0 := by omega
            subst this; simp [maxUpTo]
  | succ m ih =>
    intro k hk
    by_cases h : k = m + 1
    · subst h; simp only [maxUpTo]; exact Nat.le_max_right _ _
    · have := ih k (by omega)
      simp only [maxUpTo]; omega

/-- Wer die 1 erreicht, bleibt beschränkt. -/
theorem bounded_of_reachesOne {n : Nat} (h : ReachesOne n) : ∃ B, ∀ k, iter k n ≤ B := by
  obtain ⟨j, hj⟩ := h
  refine ⟨max (maxUpTo n j) 4, fun k => ?_⟩
  by_cases hk : k ≤ j
  · have := iter_le_maxUpTo n j k hk; omega
  · have e : iter k n = iter (k - j) 1 := by
      rw [← hj, ← iter_add, Nat.add_sub_cancel' (by omega)]
    rw [e]
    rcases iter_one_mem (k - j) with h | h | h <;> omega

/-- **Die Collatz-Vermutung ist äquivalent zu: alle Folgen sind beschränkt, und es gibt
keinen nichttrivialen Zyklus.** -/
theorem conjecture_iff :
    CollatzConjecture ↔
      ((∀ n, 0 < n → ∃ B, ∀ k, iter k n ≤ B) ∧
       (∀ n p, 0 < n → Periodic n p → n = 1 ∨ n = 4 ∨ n = 2)) := by
  constructor
  · intro hc
    exact ⟨fun n h0 => bounded_of_reachesOne (hc n h0),
      fun n p h0 hp => periodic_reachesOne hp (hc n h0)⟩
  · rintro ⟨hb, hcyc⟩ n h0
    obtain ⟨B, hB⟩ := hb n h0
    obtain ⟨k, p, hp⟩ := eventually_periodic hB
    apply reachesOne_of_iter (k := k)
    rcases hcyc _ p (iter_pos h0 k) hp with h | h | h <;> rw [h]
    · exact ⟨0, rfl⟩
    · exact ⟨2, by decide⟩
    · exact ⟨1, by decide⟩

end Collatz
