import Collatz.Density

/-!
# Die Anzahl ungerader Schritte ist binomialverteilt (Terras 1976)

Unter den `2^k` Restklassen modulo `2^k` haben genau `C(k, j)` genau `j` ungerade Schritte
unter den ersten `k` Schritten von `T`. Gleichwertig: `Σ_{r < 2^k} x^o(r) = (1 + x)^k` für
jedes `x`. Grund: Von den beiden Hochhebungen `r` und `r + 2^k` hat genau eine im Schritt
`k + 1` einen ungeraden Wert, die Paritätsfolgen verhalten sich also wie faire Münzwürfe.
-/

namespace Collatz

/-- Binomialkoeffizient über das Pascal-Dreieck. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, j + 1 => binom n j + binom n (j + 1)

/-- Von `r` und `r + 2^k` behält genau eine die Anzahl ungerader Schritte, die andere
bekommt einen dazu. -/
theorem pair_odds (k r : Nat) :
    (oddsT (k + 1) r = oddsT k r ∧ oddsT (k + 1) (r + 2 ^ k) = oddsT k r + 1) ∨
    (oddsT (k + 1) r = oddsT k r + 1 ∧ oddsT (k + 1) (r + 2 ^ k) = oddsT k r) := by
  have ha := (affine k r 1).1
  rw [Nat.mul_one] at ha
  have ho : oddsT k (r + 2 ^ k) = oddsT k r := by
    have := oddsT_add k r 1; rwa [Nat.mul_one] at this
  rw [oddsT_succ, oddsT_succ, ho, ha, Nat.mul_one]
  have h3 := three_pow_odd (oddsT k r)
  by_cases h : Titer k r % 2 = 1
  · have : ¬ (Titer k r + 3 ^ oddsT k r) % 2 = 1 := by omega
    right; rw [if_pos h, if_neg this]; omega
  · have : (Titer k r + 3 ^ oddsT k r) % 2 = 1 := by omega
    left; rw [if_neg h, if_pos this]; omega

theorem countBelow_eq_sum (p : Nat → Bool) : ∀ N,
    countBelow p N = sumBelow (fun i => if p i then 1 else 0) N := by
  intro N
  induction N with
  | zero => rfl
  | succ N ih => simp only [countBelow, sumBelow, ih]

theorem sumBelow_zero : ∀ N, sumBelow (fun _ => 0) N = 0 := by
  intro N
  induction N with
  | zero => rfl
  | succ N ih => simp only [sumBelow, ih]

/-- **Erzeugende Funktion**: `Σ_{r < 2^k} x^o(r) = (1 + x)^k`. -/
theorem sum_pow_odds (x : Nat) : ∀ k, sumBelow (fun r => x ^ oddsT k r) (2 ^ k) = (1 + x) ^ k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ 2 k, Nat.mul_two, sumBelow_add, sumBelow_add_fun]
    rw [sumBelow_congr (g := fun r => (1 + x) * x ^ oddsT k r) (2 ^ k) (fun r _ => by
      rw [Nat.add_comm (2 ^ k) r]
      rcases pair_odds k r with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, Nat.pow_succ]; show _ = (1 + x) * _
        generalize x ^ oddsT k r = y; rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm x y]
      · rw [h1, h2, Nat.pow_succ]; show _ = (1 + x) * _
        generalize x ^ oddsT k r = y; rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm x y, Nat.add_comm])]
    rw [sumBelow_mul, ih, Nat.pow_succ, Nat.mul_comm]

/-- **Binomialverteilung (Terras)**: Genau `C(k, j)` Restklassen modulo `2^k` haben genau `j`
ungerade unter den ersten `k` Schritten von `T`. -/
theorem count_odds : ∀ k j, countBelow (fun r => decide (oddsT k r = j)) (2 ^ k) = binom k j := by
  intro k
  induction k with
  | zero => intro j; cases j <;> rfl
  | succ k ih =>
    intro j
    rw [countBelow_eq_sum, Nat.pow_succ 2 k, Nat.mul_two, sumBelow_add, sumBelow_add_fun]
    have key : ∀ r, r < 2 ^ k →
        (if decide (oddsT (k + 1) r = j) then 1 else 0) +
          (if decide (oddsT (k + 1) (2 ^ k + r) = j) then 1 else 0) =
        (if decide (oddsT k r = j) then 1 else 0) + (if decide (oddsT k r + 1 = j) then 1 else 0) := by
      intro r _
      rw [Nat.add_comm (2 ^ k) r]
      rcases pair_odds k r with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
        by_cases a : oddsT k r = j <;> by_cases b : oddsT k r + 1 = j <;> simp [a, b] <;> omega
    rw [sumBelow_congr _ key, ← sumBelow_add_fun, ← countBelow_eq_sum, ← countBelow_eq_sum, ih]
    cases j with
    | zero =>
      have : countBelow (fun r => decide (oddsT k r + 1 = 0)) (2 ^ k) = 0 := by
        rw [countBelow_eq_sum]; simp only [Nat.add_one_ne_zero, decide_false]
        exact sumBelow_zero _
      rw [this]; cases k <;> rfl
    | succ j =>
      have : (fun r => decide (oddsT k r + 1 = j + 1)) = (fun r => decide (oddsT k r = j)) := by
        funext r; simp
      rw [this, ih]; simp only [binom]; omega

example : binom 10 3 = 120 := by decide

end Collatz
