import Collatz.TwoAdic
import Collatz.Counterexample

/-!
# Die Vermutung als Aussage über Paritätsfolgen

Mit der 2-adischen Sicht (`TwoAdic.lean`) lässt sich die Collatz-Vermutung exakt als Aussage
über Paritätsfolgen schreiben:

  **Collatz-Vermutung ⇔ die Paritätsfolge jeder Zahl `n > 0` endet in `1, 0, 1, 0, …`.**

Die Richtung "⇐" benutzt, dass eine natürliche Zahl durch ihre Paritätsfolge eindeutig bestimmt
ist (Satz von Terras): Hat `T^j(n)` dieselbe Paritätsfolge wie 1, so ist `T^j(n) = 1`.
-/

namespace Collatz

/-- Ab 1 wechselt `T` zwischen 1 und 2. -/
theorem Titer_one : ∀ i, Titer (2 * i) 1 = 1 ∧ Titer (2 * i + 1) 1 = 2 := by
  intro i
  induction i with
  | zero => exact ⟨rfl, rfl⟩
  | succ i ih =>
    refine ⟨by rw [show 2 * (i + 1) = 2 * i + 2 by omega, Titer_add, ih.1]; rfl, ?_⟩
    rw [show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by omega, Titer_add, ih.2]; rfl

/-- Die Paritätsfolge von 1 ist `1, 0, 1, 0, …`. -/
theorem nthPar_one (i : Nat) : nthPar i 1 = (i % 2 == 0) := by
  obtain ⟨h0, h1⟩ := Titer_one (i / 2)
  unfold nthPar
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [show i = 2 * (i / 2) by omega, h0]; simp
  · rw [show i = 2 * (i / 2) + 1 by omega, h1]; simp

theorem lt_two_pow' : ∀ m, m < 2 ^ m := by
  intro m
  induction m with
  | zero => decide
  | succ m ih => rw [Nat.pow_succ]; omega

/-- **Eine Zahl mit der Paritätsfolge von 1 ist 1.** -/
theorem eq_one_of_nthPar {m : Nat} (h : ∀ i, nthPar i m = (i % 2 == 0)) : m = 1 := by
  have hk : parVec (m + 1) m = parVec (m + 1) 1 := by
    rw [parVec_eq_map, parVec_eq_map]
    apply List.map_congr_left
    intro i _
    rw [h, nthPar_one]
  have hm : m < 2 ^ (m + 1) := by have := lt_two_pow' m; rw [Nat.pow_succ]; omega
  have h1 : 1 < 2 ^ (m + 1) := by have := lt_two_pow' (m + 1); omega
  exact parVec_injective _ _ _ hm h1 hk

/-- **Die Vermutung als Aussage über Paritätsfolgen.** -/
theorem conjecture_iff_parity :
    CollatzConjecture ↔ ∀ n, 0 < n → ∃ j, ∀ i, nthPar (j + i) n = (i % 2 == 0) := by
  constructor
  · intro H n hn
    obtain ⟨j, hj⟩ := (reachesOne_iff_T n).mp (H n hn)
    refine ⟨j, fun i => ?_⟩
    unfold nthPar
    rw [Titer_add, hj]
    exact nthPar_one i
  · intro H n hn
    obtain ⟨j, hj⟩ := H n hn
    apply (reachesOne_iff_T n).mpr
    refine ⟨j, eq_one_of_nthPar fun i => ?_⟩
    have := hj i
    unfold nthPar at this ⊢
    rwa [Titer_add] at this

end Collatz
