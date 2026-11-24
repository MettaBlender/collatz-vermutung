import Collatz.CycleBasin

/-!
# Satz 53: Ungerade Vorfahren gibt es in jedem Intervall `[y, 4y]`

Ist `c` ungerade mit `3c + 1 = 2^E · n`, dann auch `c' = 4c + 1`, denn
`3(4c+1) + 1 = 4(3c+1) = 2^(E+2) · n`. Die ungeraden direkten Vorfahren von `n`
bilden also eine Kette `c₀, 4c₀+1, 16c₀+5, …`, jedes Glied etwa viermal so gross wie das vorige.
Darum liegt für jedes `y ≥ n` ein ungerader Vorfahre von `n` zwischen `y` und `4y`.

Folgerungen:
* Ungerade Zahlen, die die 1 erreichen, gibt es in jedem Intervall `[y, 4y]` (`y ≥ 1`).
* Gäbe es ein Gegenbeispiel, dann gäbe es ein `n` mit ungeraden Gegenbeispielen in **jedem**
  Intervall `[y, 4y]` mit `y ≥ n`. Gegenbeispiele hätten also keine grossen Lücken.
-/

namespace Collatz

/-- Ein ungerader direkter Vorfahre: `3c + 1 = 2^E · n`. -/
def DirectOdd (n c : Nat) : Prop := c % 2 = 1 ∧ ∃ E, 3 * c + 1 = 2 ^ E * n

theorem DirectOdd.reaches {n c : Nat} (h : DirectOdd n c) : ∃ i, iter i c = n := by
  obtain ⟨h1, E, hE⟩ := h
  refine ⟨E + 1, ?_⟩
  rw [iter_succ, step_odd h1, hE, iter_two_pow_mul]

theorem DirectOdd.next {n c : Nat} (h : DirectOdd n c) : DirectOdd n (4 * c + 1) := by
  obtain ⟨h1, E, hE⟩ := h
  refine ⟨by omega, E + 2, ?_⟩
  rw [Nat.pow_add, Nat.mul_comm (2 ^ E) (2 ^ 2), Nat.mul_assoc, ← hE]
  omega

theorem directOdd_base {n : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) :
    ∃ c, DirectOdd n c ∧ 3 * c ≤ 4 * n := by
  have hn : n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases hn with h | h | h | h
  · exact ⟨(4 * n - 1) / 3, ⟨by omega, 2, by omega⟩, by omega⟩
  · exact ⟨(2 * n - 1) / 3, ⟨by omega, 1, by omega⟩, by omega⟩
  · exact ⟨(4 * n - 1) / 3, ⟨by omega, 2, by omega⟩, by omega⟩
  · exact ⟨(2 * n - 1) / 3, ⟨by omega, 1, by omega⟩, by omega⟩

theorem directOdd_interval_aux {n c₀ : Nat} (hb : DirectOdd n c₀) :
    ∀ y, ∃ c, DirectOdd n c ∧ y ≤ c ∧ (c ≤ 4 * y ∨ c = c₀) := by
  intro y
  induction y with
  | zero => exact ⟨c₀, hb, Nat.zero_le _, Or.inr rfl⟩
  | succ y ih =>
    obtain ⟨c, hc, hy, hle⟩ := ih
    by_cases hlt : y + 1 ≤ c
    · exact ⟨c, hc, hlt, by omega⟩
    · have : c = y := by omega
      exact ⟨4 * c + 1, hc.next, by omega, by omega⟩

/-- **Satz 53.** Jede Zahl `n > 0` mit `3 ∤ n` hat für jedes `y ≥ n` einen ungeraden
Vorfahren `c` mit `y ≤ c ≤ 4y`. -/
theorem odd_ancestor_in_interval {n : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) :
    ∀ y, n ≤ y → ∃ c, c % 2 = 1 ∧ y ≤ c ∧ c ≤ 4 * y ∧ ∃ i, iter i c = n := by
  intro y hy
  obtain ⟨c₀, hb, hc₀⟩ := directOdd_base h0 h3
  obtain ⟨c, hc, hyc, hle⟩ := directOdd_interval_aux hb y
  exact ⟨c, hc.1, hyc, by omega, hc.reaches⟩

/-- Ungerade Zahlen, die die 1 erreichen, gibt es in jedem Intervall `[y, 4y]`. -/
theorem odd_reaching_one_in_interval :
    ∀ y, 1 ≤ y → ∃ c, c % 2 = 1 ∧ y ≤ c ∧ c ≤ 4 * y ∧ ReachesOne c := by
  intro y hy
  obtain ⟨c, h1, h2, h3, hr⟩ := odd_ancestor_in_interval (n := 1) (by decide) (by decide) y hy
  exact ⟨c, h1, h2, h3, hr⟩

/-- Gäbe es ein Gegenbeispiel, dann gäbe es ein `n`, so dass jedes Intervall `[y, 4y]`
mit `y ≥ n` ein ungerades Gegenbeispiel enthält. -/
theorem counterexamples_no_gaps (h : ¬ CollatzConjecture) :
    ∃ n, 0 < n ∧ ∀ y, n ≤ y → ∃ c, c % 2 = 1 ∧ y ≤ c ∧ c ≤ 4 * y ∧ ¬ ReachesOne c := by
  obtain ⟨n, hn, hr⟩ : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact h (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  obtain ⟨n', hn', h3', hr'⟩ := counterexample_not_three n hn hr
  refine ⟨n', hn', fun y hy => ?_⟩
  obtain ⟨c, h1, h2, h3, j, hj⟩ := odd_ancestor_in_interval hn' h3' y hy
  exact ⟨c, h1, h2, h3, fun hc => hr' (hj ▸ reachesOne_iter hc j)⟩

end Collatz
