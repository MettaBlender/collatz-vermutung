import Collatz.Reduction

/-!
# Beliebig lange Anstiege

Zahlen der Form `2^k·a − 1` fallen `2k` Schritte lang nie unter ihren Startwert und landen bei

    2^k·a − 1  →  …  →  3^k·a − 1.

Insbesondere gibt es keine feste Schrittzahl, nach der jede Zahl kleiner geworden ist.
Daraus folgt (informell), dass kein Restklassen-Sieb modulo `2^k` alle Klassen erledigt: die Klasse
`2^k − 1` bleibt immer offen.
-/

namespace Collatz

/-- Zwei Schritte: `2y − 1 → 6y − 2 → 3y − 1` (für `y ≥ 1`). -/
theorem iter_two_climb {y : Nat} (hy : 1 ≤ y) : iter 2 (2 * y - 1) = 3 * y - 1 := by
  have e1 : step (2 * y - 1) = 6 * y - 2 := by rw [step_odd (by omega)]; omega
  have e2 : step (6 * y - 2) = 3 * y - 1 := by rw [step_even (by omega)]; omega
  simp only [iter_succ, iter_zero, e1, e2]

private theorem pow_succ_mul (k a : Nat) : 2 ^ (k + 1) * a = 2 * (2 ^ k * a) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]

private theorem pow_mul_three (k a : Nat) : 2 ^ k * (3 * a) = 3 * (2 ^ k * a) := by
  rw [Nat.mul_left_comm]

private theorem pow_pos_mul {k a : Nat} (ha : 1 ≤ a) : 1 ≤ 2 ^ k * a :=
  Nat.mul_pos (Nat.pow_pos (by decide)) ha

/-- **Nach `2k` Schritten wird aus `2^k·a − 1` die Zahl `3^k·a − 1`.** -/
theorem iter_climb (k : Nat) : ∀ a, 1 ≤ a → iter (2 * k) (2 ^ k * a - 1) = 3 ^ k * a - 1 := by
  induction k with
  | zero => intro a _; simp
  | succ k ih =>
    intro a ha
    have hy := pow_pos_mul (k := k) ha
    have h2 : 2 * (k + 1) = 2 + 2 * k := by omega
    rw [h2, iter_add, pow_succ_mul, iter_two_climb hy, ← pow_mul_three,
      ih (3 * a) (by omega), Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 3 a]

/-- **Unterwegs fällt die Folge nie unter den Startwert**: Für alle `j ≤ 2k` gilt
`2^k·a − 1 ≤ iter j (2^k·a − 1)`. -/
theorem climb_ge (k : Nat) : ∀ a, 1 ≤ a → ∀ j, j ≤ 2 * k →
    2 ^ k * a - 1 ≤ iter j (2 ^ k * a - 1) := by
  induction k with
  | zero => intro a _ j hj; have : j = 0 := by omega
            subst this; simp
  | succ k ih =>
    intro a ha j hj
    have hy := pow_pos_mul (k := k) ha
    rw [pow_succ_mul]
    match j, hj with
    | 0, _ => simp
    | 1, _ =>
      simp only [iter_succ, iter_zero]
      rw [step_odd (by omega)]; omega
    | j + 2, hj =>
      rw [Nat.add_comm j 2, iter_add, iter_two_climb hy, ← pow_mul_three]
      have := ih (3 * a) (by omega) j (by omega)
      rw [pow_mul_three] at this ⊢
      omega

/-- **Es gibt keine feste Abstiegszeit**: Für jedes `K` gibt es eine Zahl `n > 1`,
die in den ersten `K` Schritten nie unter `n` fällt. -/
theorem no_uniform_descent (K : Nat) : ∃ n, 1 < n ∧ ∀ j, j ≤ K → n ≤ iter j n := by
  refine ⟨2 ^ (K + 2) * 1 - 1, ?_, fun j hj => climb_ge (K + 2) 1 (by decide) j (by omega)⟩
  have h : 2 ^ 2 ≤ 2 ^ (K + 2) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.mul_one]
  have : (2 : Nat) ^ 2 = 4 := rfl
  omega

/-- Beispiel: `2^10 − 1 = 1023` wird nach 20 Schritten zu `3^10 − 1 = 59048`. -/
example : iter 20 1023 = 59048 := by decide

end Collatz
