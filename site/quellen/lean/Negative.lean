import Collatz.Basic

/-!
# Collatz auf den negativen ganzen Zahlen

Dieselbe Regel `n/2` bzw. `3n+1` auf ganzen Zahlen (`Int`) hat bei negativen Zahlen
**drei verschiedene Zyklen**: `-1 → -2 → -1`, einen der Länge 5 durch `-5` und einen
der Länge 18 durch `-17`. (Das ist dasselbe wie die Regel `3n-1` auf positiven Zahlen.)

Lehre daraus: Ein Beweis der Collatz-Vermutung muss benutzen, dass die Zahlen positiv
sind. Jedes Argument, das nur mit Paritäten, Restklassen oder der Zyklusgleichung
arbeitet und für negative Zahlen genauso gilt, kann die Vermutung nicht beweisen.
-/

namespace Collatz

/-- Ein Collatz-Schritt auf ganzen Zahlen. -/
def stepZ (n : Int) : Int := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `k` Schritte auf ganzen Zahlen. -/
def iterZ : Nat → Int → Int
  | 0, n => n
  | k + 1, n => iterZ k (stepZ n)

/-- Für positive Zahlen ist es die gewöhnliche Collatz-Abbildung. -/
theorem stepZ_natCast (n : Nat) : stepZ (n : Int) = (step n : Int) := by
  unfold stepZ step
  split <;> split <;> omega

theorem iterZ_natCast (k n : Nat) : iterZ k (n : Int) = (iter k n : Int) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [iterZ, iter_succ, stepZ_natCast, ih]

/-- Der Zyklus `-1 → -2 → -1`. -/
theorem cycle_neg1 : iterZ 2 (-1) = -1 := by decide

/-- Der Zyklus der Länge 5: `-5 → -14 → -7 → -20 → -10 → -5`. -/
theorem cycle_neg5 : iterZ 5 (-5) = -5 := by decide

/-- Der Zyklus der Länge 18 durch `-17`. -/
theorem cycle_neg17 : iterZ 18 (-17) = -17 := by decide

/-- Die Zyklen sind wirklich verschieden: Kein Glied des 5er- oder 18er-Zyklus ist
`-1`, `-2`, und die beiden Zyklen haben kein gemeinsames Glied. -/
def cycleNeg5 : List Int := [-5, -14, -7, -20, -10]
def cycleNeg17 : List Int :=
  [-17, -50, -25, -74, -37, -110, -55, -164, -82, -41, -122, -61, -182, -91, -272,
   -136, -68, -34]

theorem cycleNeg5_orbit : ∀ i, i < 5 → iterZ i (-5) ∈ cycleNeg5 := by decide
theorem cycleNeg17_orbit : ∀ i, i < 18 → iterZ i (-17) ∈ cycleNeg17 := by decide

/-- **Satz 23: Auf den negativen Zahlen gibt es drei verschiedene Collatz-Zyklen.** -/
theorem three_negative_cycles :
    iterZ 2 (-1) = -1 ∧ iterZ 5 (-5) = -5 ∧ iterZ 18 (-17) = -17 ∧
    (∀ x ∈ cycleNeg5, x ∉ cycleNeg17 ∧ x ≠ -1 ∧ x ≠ -2) ∧
    (∀ x ∈ cycleNeg17, x ≠ -1 ∧ x ≠ -2) := by
  refine ⟨cycle_neg1, cycle_neg5, cycle_neg17, by decide, by decide⟩

end Collatz
