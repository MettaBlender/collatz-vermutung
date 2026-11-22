import Collatz.Density
import Collatz.VerifiedHugeAll

/-!
# Wie ein Gegenbeispiel aussehen müsste

Alles zusammen: Erreicht `n` die 1 nicht, so hat seine Folge ein kleinstes Glied `m` mit

* `m ≥ 2^22` (Satz 13),
* `m mod 2^20` in einer der 27 328 offenen Restklassen (Satz 13),
* in den ersten `k` Schritten von `T` (für jedes `k` mit `2^k ≤ m`) so viele ungerade Schritte,
  dass `2^k < 2·3^o` gilt, also mindestens etwa 63 % (Satz 15). Für `k = 22` heisst das:
  mindestens 14 ungerade unter den ersten 22 Schritten.

Ausserdem: Die Vermutung ist für `T` dieselbe wie für die gewöhnliche Collatz-Abbildung.
-/

namespace Collatz

/-- Das kleinste Glied einer Folge hat am Anfang viele ungerade Schritte. -/
theorem orbitMin_many_odds {m k : Nat} (hmin : IsOrbitMin m) (hk : 2 ^ k ≤ m) :
    2 ^ k < 2 * 3 ^ oddsT k m := by
  apply Nat.lt_of_not_le
  intro hle
  obtain ⟨j, hj⟩ := descends_of_few_odds hk hle
  exact absurd (hmin j) (by omega)

/-- **Struktur eines Gegenbeispiels.** -/
theorem counterexample_profile {n : Nat} (h0 : 0 < n) (h : ¬ ReachesOne n) :
    ∃ k, 4194304 ≤ iter k n ∧ IsOrbitMin (iter k n) ∧ iter k n % 1048576 ∈ survivors20 ∧
      (∀ j, 2 ^ j ≤ iter k n → 2 ^ j < 2 * 3 ^ oddsT j (iter k n)) ∧
      14 ≤ oddsT 22 (iter k n) := by
  obtain ⟨k, hbig, hmin, hmod⟩ := counterexample_structure22 h0 h
  have hodd : ∀ j, 2 ^ j ≤ iter k n → 2 ^ j < 2 * 3 ^ oddsT j (iter k n) :=
    fun j hj => orbitMin_many_odds hmin hj
  refine ⟨k, hbig, hmin, hmod, hodd, ?_⟩
  have h22 := hodd 22 (by have : (2 : Nat) ^ 22 = 4194304 := rfl; omega)
  apply Nat.le_of_not_lt
  intro hlt
  have : 3 ^ oddsT 22 (iter k n) ≤ 3 ^ 13 := Nat.pow_le_pow_right (by decide) (by omega)
  have e1 : (3 : Nat) ^ 13 = 1594323 := rfl
  have e2 : (2 : Nat) ^ 22 = 4194304 := rfl
  omega

/-! ## Die Vermutung für `T` -/

theorem Titer_add (a b n : Nat) : Titer (a + b) n = Titer b (Titer a n) := by
  induction a generalizing n with
  | zero => simp [Titer]
  | succ a ih => rw [Nat.add_right_comm]; simp only [Titer]; exact ih (T n)

/-- **`n` erreicht die 1 genau dann, wenn die beschleunigte Folge `T` die 1 erreicht.** -/
theorem reachesOne_iff_T (n : Nat) : ReachesOne n ↔ ∃ k, Titer k n = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    induction k using Nat.strongRecOn generalizing n with
    | _ k ih =>
      by_cases h1 : n = 1
      · exact ⟨0, h1⟩
      by_cases he : n % 2 = 0
      · -- gerader Schritt: T n = n / 2 = step n
        match k, hk with
        | 0, hk => exact absurd hk h1
        | k + 1, hk =>
          have hs : step n = T n := by unfold T; rw [if_pos he, step_even he]
          rw [iter_succ, hs] at hk
          obtain ⟨j, hj⟩ := ih k (by omega) (T n) hk
          exact ⟨j + 1, hj⟩
      · -- ungerade: zwei Schritte 3n+1, dann halbieren
        match k, hk with
        | 0, hk => exact absurd hk h1
        | 1, hk =>
          simp only [iter_succ, iter_zero, step_odd (by omega : n % 2 = 1)] at hk; omega
        | k + 2, hk =>
          have h2 : iter 2 n = T n := by
            unfold T; rw [if_neg he]; exact iter_two_odd (by omega)
          rw [Nat.add_comm, iter_add, h2] at hk
          obtain ⟨j, hj⟩ := ih k (by omega) (T n) hk
          exact ⟨j + 1, hj⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + oddsT k n, by rw [← Titer_eq_iter]; exact hk⟩

end Collatz
