import Collatz.ManyCounterexamples
import Collatz.Binomial

/-!
# Der gewichtete Crandall-Baum: Exponent 0.291 statt 0.224

Im Baum aus Satz 34/40 hat jeder Knoten `n` zwei Kinder. Die Schranke `c < 22·n` ist nur für das
Kind `child n true` nötig, das andere Kind ist viel kleiner: `child n false < 6·n`.

Zählt man für einen Weg der Länge `t`, wie oft er das kleine Kind nimmt (`zeros t k = a`), so gilt

* `nodeAt r t k ≤ r · 6^a · 22^(t−a)` (`weighted_le`),
* genau `C(t, a)` Wege haben `a` kleine Schritte (`count_zeros`).

**Satz** (`weighted_many_reach_one`): Für alle `t` und `a ≤ t` gibt es `C(t,a)` verschiedene Zahlen
`≤ 5·6^a·22^(t−a)`, die die 1 erreichen. Optimiert man über `a`, so ergibt sich für jedes `x` eine
Anzahl von etwa `x^α` Zahlen `≤ x` mit `6^(−α) + 22^(−α) = 1`, also `α ≈ 0.2912` statt
`log 2 / log 22 ≈ 0.224`.

Mit der Wurzel `r` eines hypothetischen Gegenbeispiels gilt dasselbe für Gegenbeispiele
(`weighted_many_counterexamples`).
-/

namespace Collatz

/-- Das kleine Kind ist kleiner als `6·n`. -/
theorem child_false_lt {n : Nat} (h1 : n % 2 = 1) (h3 : n % 3 ≠ 0) : child n false < 6 * n := by
  obtain ⟨_, hc⟩ := firstAnc_spec h1 h3
  unfold child
  simp only [Bool.false_eq_true, if_false]
  generalize firstAnc n = c at hc
  by_cases h : c % 3 = 0
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- Anzahl der kleinen Schritte (`Bit = 0`) auf dem Weg `k` der Länge `t`. -/
def zeros : Nat → Nat → Nat
  | 0, _ => 0
  | t + 1, k => zeros t (k / 2) + (if k % 2 = 1 then 0 else 1)

theorem zeros_le : ∀ t k, zeros t k ≤ t := by
  intro t
  induction t with
  | zero => intro k; exact Nat.le_refl 0
  | succ t ih =>
    intro k
    have := ih (k / 2)
    show zeros t (k / 2) + (if k % 2 = 1 then 0 else 1) ≤ t + 1
    split <;> omega

/-- **Gewichtete Grössenschranke.** -/
theorem weighted_le {r : Nat} (h1 : r % 2 = 1) (h3 : r % 3 ≠ 0) :
    ∀ t k, nodeAt r t k ≤ r * 6 ^ zeros t k * 22 ^ (t - zeros t k) := by
  intro t
  induction t with
  | zero => intro k; simp [nodeAt, zeros]
  | succ t ih =>
    intro k
    obtain ⟨a, b⟩ := nodeAt_spec h1 h3 t (k / 2)
    have hz := zeros_le t (k / 2)
    have hi := ih (k / 2)
    show child (nodeAt r t (k / 2)) (k % 2 == 1) ≤
      r * 6 ^ (zeros t (k / 2) + (if k % 2 = 1 then 0 else 1)) *
        22 ^ (t + 1 - (zeros t (k / 2) + (if k % 2 = 1 then 0 else 1)))
    generalize zeros t (k / 2) = z at hz hi
    by_cases hk : k % 2 = 1
    · have hb : (k % 2 == 1) = true := by simp [hk]
      rw [hb, if_pos hk]
      have hc := child_lt a b true
      have := Nat.mul_le_mul_left 22 hi
      have e : t + 1 - (z + 0) = (t - z) + 1 := by omega
      rw [e, Nat.add_zero, Nat.pow_succ]
      have e2 : 22 * (r * 6 ^ z * 22 ^ (t - z)) = r * 6 ^ z * (22 ^ (t - z) * 22) := by grind
      omega
    · have hb : (k % 2 == 1) = false := by simp [hk]
      rw [hb, if_neg hk]
      have hc := child_false_lt a b
      have := Nat.mul_le_mul_left 6 hi
      have e : t + 1 - (z + 1) = t - z := by omega
      rw [e, Nat.pow_succ]
      have e2 : 6 * (r * 6 ^ z * 22 ^ (t - z)) = r * (6 ^ z * 6) * 22 ^ (t - z) := by grind
      omega

/-- Summe über `2N` als Summe über Paare `(2i, 2i+1)`. -/
theorem sumBelow_two_mul (f : Nat → Nat) : ∀ N,
    sumBelow f (2 * N) = sumBelow (fun i => f (2 * i) + f (2 * i + 1)) N := by
  intro N
  induction N with
  | zero => rfl
  | succ N ih =>
    have e : 2 * (N + 1) = 2 * N + 1 + 1 := by omega
    rw [e]
    show sumBelow f (2 * N) + f (2 * N) + f (2 * N + 1) = _ + _
    rw [ih]; show _ = _ + (f (2 * N) + f (2 * N + 1)); omega

/-- **Zählung.** Genau `C(t, a)` Wege der Länge `t` nehmen `a`-mal das kleine Kind. -/
theorem count_zeros : ∀ t a, countBelow (fun k => decide (zeros t k = a)) (2 ^ t) = binom t a := by
  intro t
  induction t with
  | zero => intro a; cases a <;> rfl
  | succ t ih =>
    intro a
    rw [countBelow_eq_sum, Nat.pow_succ, Nat.mul_comm, sumBelow_two_mul]
    have key : ∀ i, i < 2 ^ t →
        (if decide (zeros (t + 1) (2 * i) = a) then 1 else 0) +
          (if decide (zeros (t + 1) (2 * i + 1) = a) then 1 else 0) =
        (if decide (zeros t i = a) then 1 else 0) + (if decide (zeros t i + 1 = a) then 1 else 0) := by
      intro i _
      have e0 : zeros (t + 1) (2 * i) = zeros t i + 1 := by
        show zeros t (2 * i / 2) + (if 2 * i % 2 = 1 then 0 else 1) = _
        rw [if_neg (by omega)]; congr 2; omega
      have e1 : zeros (t + 1) (2 * i + 1) = zeros t i := by
        show zeros t ((2 * i + 1) / 2) + (if (2 * i + 1) % 2 = 1 then 0 else 1) = _
        rw [if_pos (by omega)]; rw [Nat.add_zero]; congr 1; omega
      rw [e0, e1]
      by_cases x : zeros t i = a <;> by_cases y : zeros t i + 1 = a <;> simp [x, y] <;> omega
    rw [sumBelow_congr _ key, ← sumBelow_add_fun, ← countBelow_eq_sum, ← countBelow_eq_sum, ih]
    cases a with
    | zero =>
      have : countBelow (fun r => decide (zeros t r + 1 = 0)) (2 ^ t) = 0 := by
        rw [countBelow_eq_sum]; simp only [Nat.add_one_ne_zero, decide_false]
        exact sumBelow_zero _
      rw [this]; cases t <;> rfl
    | succ a =>
      have : (fun r => decide (zeros t r + 1 = a + 1)) = (fun r => decide (zeros t r = a)) := by
        funext r; simp
      rw [this, ih]; simp only [binom]; omega

/-- **Satz (gewichteter Crandall-Baum, für alle `t`, `a`).** Die `C(t,a)` Wege `k < 2^t` mit
`zeros t k = a` liefern verschiedene Zahlen `nodeAt 5 t k ≤ 5·6^a·22^(t−a)`, die alle die 1
erreichen. -/
theorem weighted_many_reach_one (t a : Nat) :
    countBelow (fun k => decide (zeros t k = a)) (2 ^ t) = binom t a ∧
    (∀ k, k < 2 ^ t → zeros t k = a →
      nodeAt 5 t k ≤ 5 * 6 ^ a * 22 ^ (t - a) ∧ ReachesOne (nodeAt 5 t k)) ∧
    (∀ k k', k < 2 ^ t → k' < 2 ^ t → nodeAt 5 t k = nodeAt 5 t k' → k = k') := by
  have h1 : (5 : Nat) % 2 = 1 := by decide
  have h3 : (5 : Nat) % 3 ≠ 0 := by decide
  refine ⟨count_zeros t a, fun k _ hz => ⟨?_, ?_⟩, nodeAt_injective h1 h3 t⟩
  · have := weighted_le h1 h3 t k; rwa [hz] at this
  · obtain ⟨j, hj⟩ := nodeAt_reaches h1 h3 t k
    exact ⟨5 + j, by rw [Nat.add_comm, iter_add, hj]; decide⟩

/-- **Gegenbeispiel-Version.** Gäbe es ein Gegenbeispiel, so gäbe es eines `r` (ungerade, `3 ∤ r`),
und für alle `t`, `a` hätte man `C(t,a)` verschiedene Gegenbeispiele `≤ r·6^a·22^(t−a)`. -/
theorem weighted_many_counterexamples (h : ¬ CollatzConjecture) :
    ∃ r, r % 2 = 1 ∧ r % 3 ≠ 0 ∧ ∀ t a,
      countBelow (fun k => decide (zeros t k = a)) (2 ^ t) = binom t a ∧
      (∀ k, k < 2 ^ t → zeros t k = a →
        nodeAt r t k ≤ r * 6 ^ a * 22 ^ (t - a) ∧ ¬ ReachesOne (nodeAt r t k)) ∧
      (∀ k k', k < 2 ^ t → k' < 2 ^ t → nodeAt r t k = nodeAt r t k' → k = k') := by
  obtain ⟨n, hn, hr⟩ : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact h (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  obtain ⟨n', hn', h3', hr'⟩ := counterexample_not_three n hn hr
  obtain ⟨r, _, h1, h3, hrr⟩ := counterexample_odd_not_three n' hn' h3' hr'
  refine ⟨r, h1, h3, fun t a => ⟨count_zeros t a, fun k _ hz => ⟨?_, ?_⟩, nodeAt_injective h1 h3 t⟩⟩
  · have := weighted_le h1 h3 t k; rwa [hz] at this
  · intro hk
    obtain ⟨j, hj⟩ := nodeAt_reaches h1 h3 t k
    exact hrr (hj ▸ reachesOne_iter hk j)

end Collatz
