import Collatz.Cycles
import Collatz.Tree

/-!
# Vielfache von 3 liegen auf keinem Zyklus

Ein Schritt macht aus einer Zahl, die nicht durch 3 teilbar ist, nie ein Vielfaches
von 3: `3n + 1 ≡ 1 (mod 3)`, und `n/2` ist durch 3 teilbar nur, wenn `n` es ist.
Eine Folge bleibt also höchstens am Anfang bei Vielfachen von 3, und zwar nur so lange,
wie sie halbiert. Daraus folgt: **Kein Zyklus enthält ein Vielfaches von 3.**
-/

namespace Collatz

/-- Wer nicht durch 3 teilbar ist, bleibt es nach einem Schritt. -/
theorem step_not_mul_three {n : Nat} (h : n % 3 ≠ 0) : step n % 3 ≠ 0 := by
  unfold step; split <;> omega

/-- … und nach beliebig vielen Schritten. -/
theorem iter_not_mul_three {n : Nat} (h : n % 3 ≠ 0) : ∀ k, iter k n % 3 ≠ 0 := by
  intro k
  induction k generalizing n with
  | zero => simpa using h
  | succ k ih => rw [iter_succ]; exact ih (step_not_mul_three h)

/-- Nach einem `3n+1`-Schritt ist die Zahl `≡ 1 (mod 3)`. -/
theorem step_odd_mod_three {n : Nat} (h : n % 2 = 1) : step n % 3 = 1 := by
  rw [step_odd h]; omega

/-- Solange die Folge ab einem Vielfachen von 3 bei Vielfachen von 3 bleibt, wurde
nur halbiert: `2^k · iter k n = n`. -/
theorem mul_three_prefix (n : Nat) :
    ∀ k, iter k n % 3 ≠ 0 ∨ (iter k n % 3 = 0 ∧ 2 ^ k * iter k n = n) := by
  intro k
  induction k with
  | zero => by_cases h : n % 3 = 0 <;> simp [h]
  | succ k ih =>
    rw [iter_add k 1]
    show (step (iter k n)) % 3 ≠ 0 ∨ (step (iter k n) % 3 = 0 ∧ 2 ^ (k + 1) * step (iter k n) = n)
    rcases ih with h | ⟨h3, hk⟩
    · exact Or.inl (step_not_mul_three h)
    · by_cases he : iter k n % 2 = 0
      · rw [step_even he]
        refine Or.inr ⟨by omega, ?_⟩
        rw [Nat.pow_succ, Nat.mul_assoc, show 2 * (iter k n / 2) = iter k n by omega]
        exact hk
      · left; rw [step_odd (by omega)]; omega

/-- **Satz 22: Kein Zyklus enthält ein Vielfaches von 3.** -/
theorem periodic_not_mul_three {n p : Nat} (hp : Periodic n p) (h0 : 0 < n) :
    n % 3 ≠ 0 := by
  intro h3
  rcases mul_three_prefix n p with h | ⟨_, hk⟩
  · rw [hp.2] at h; exact h h3
  · rw [hp.2] at hk
    have : 2 ≤ 2 ^ p := by
      have := Nat.pow_le_pow_right (show 0 < 2 by omega) hp.1
      simpa using this
    have : 2 * n ≤ 2 ^ p * n := Nat.mul_le_mul_right n this
    omega

/-- Für jede Zahl `n ≥ 1` gilt nach `n` Schritten: ab da kommt kein Vielfaches von 3
mehr vor (die Halbierungsphase am Anfang ist kürzer als `n`). -/
theorem eventually_not_mul_three {n : Nat} (h0 : 0 < n) :
    ∀ k, n ≤ k → iter k n % 3 ≠ 0 := by
  intro k hk
  rcases mul_three_prefix n k with h | ⟨_, hk2⟩
  · exact h
  · exfalso
    have hlt : k < 2 ^ k := Nat.lt_two_pow_self
    by_cases hz : iter k n = 0
    · rw [hz] at hk2; omega
    · have : 2 ^ k ≤ 2 ^ k * iter k n := Nat.le_mul_of_pos_right _ (by omega)
      omega

/-- **Der Baum über einem Vielfachen von 3 ist ein einzelner Strahl**: Wer in `k`
Schritten bei einem Vielfachen `n` von 3 ankommt, ist `2^k · n`. -/
theorem preimage_mul_three {n : Nat} (h3 : n % 3 = 0) :
    ∀ k m, iter k m = n → m = 2 ^ k * n := by
  intro k
  induction k with
  | zero => intro m h; simpa using h
  | succ k ih =>
    intro m h
    rw [iter_succ] at h
    have hs := ih (step m) h
    have h3' : (2 ^ k * n) % 3 = 0 := by
      rw [Nat.mul_mod, h3]; simp
    rw [pred_of_mul_three h3' hs, Nat.pow_succ]
    rw [Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]

end Collatz
