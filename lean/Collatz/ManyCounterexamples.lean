import Collatz.Crandall
import Collatz.DenseTree

/-!
# Gäbe es ein Gegenbeispiel, dann gäbe es viele

Der Baum aus Satz 34 funktioniert mit **jeder** Wurzel `r` (ungerade, `3 ∤ r`), nicht nur mit 5.
Alle Knoten erreichen `r`. Ist `r` ein Gegenbeispiel, so sind es alle Knoten.

**Satz** (`many_counterexamples`): Gäbe es ein Gegenbeispiel, dann gäbe es ein ungerades
Gegenbeispiel `r` mit `3 ∤ r` und für jedes `t` mindestens `2^t` verschiedene Gegenbeispiele
`≤ r · 22^t`. Ihre Anzahl unter `x` wäre also mindestens `½ · (x/r)^0.224` (für `x ≥ r`).

Das widerspricht nicht den Dichte-Sätzen (15, 28, 33): `x^0.224` ist immer noch Dichte 0.
-/

namespace Collatz

/-- Der Baum über der Wurzel `r`. -/
def nodeAt (r : Nat) : Nat → Nat → Nat
  | 0, _ => r
  | t + 1, k => child (nodeAt r t (k / 2)) (k % 2 == 1)

theorem nodeAt_spec {r : Nat} (h1 : r % 2 = 1) (h3 : r % 3 ≠ 0) :
    ∀ t k, nodeAt r t k % 2 = 1 ∧ nodeAt r t k % 3 ≠ 0 := by
  intro t
  induction t with
  | zero => intro k; exact ⟨h1, h3⟩
  | succ t ih =>
    intro k
    obtain ⟨a, b⟩ := ih (k / 2)
    obtain ⟨c1, c3, _⟩ := child_spec a b (k % 2 == 1)
    exact ⟨c1, c3⟩

/-- Jeder Knoten erreicht die Wurzel. -/
theorem nodeAt_reaches {r : Nat} (h1 : r % 2 = 1) (h3 : r % 3 ≠ 0) :
    ∀ t k, ∃ j, iter j (nodeAt r t k) = r := by
  intro t
  induction t with
  | zero => intro k; exact ⟨0, rfl⟩
  | succ t ih =>
    intro k
    obtain ⟨a, b⟩ := nodeAt_spec h1 h3 t (k / 2)
    obtain ⟨j, hj⟩ := child_reaches a b (k % 2 == 1)
    obtain ⟨i, hi⟩ := ih (k / 2)
    exact ⟨j + i, by
      show iter (j + i) (child (nodeAt r t (k / 2)) (k % 2 == 1)) = r
      rw [iter_add, hj, hi]⟩

theorem nodeAt_le {r : Nat} (h1 : r % 2 = 1) (h3 : r % 3 ≠ 0) :
    ∀ t k, nodeAt r t k ≤ r * 22 ^ t := by
  intro t
  induction t with
  | zero => intro k; simp [nodeAt]
  | succ t ih =>
    intro k
    obtain ⟨a, b⟩ := nodeAt_spec h1 h3 t (k / 2)
    have hc := child_lt a b (k % 2 == 1)
    have := Nat.mul_le_mul_left 22 (ih (k / 2))
    show child (nodeAt r t (k / 2)) (k % 2 == 1) ≤ r * 22 ^ (t + 1)
    have e : 22 * (r * 22 ^ t) = r * 22 ^ (t + 1) := by rw [Nat.pow_succ]; grind
    omega

theorem nodeAt_injective {r : Nat} (h1 : r % 2 = 1) (h3 : r % 3 ≠ 0) :
    ∀ t k k', k < 2 ^ t → k' < 2 ^ t → nodeAt r t k = nodeAt r t k' → k = k' := by
  intro t
  induction t with
  | zero => intro k k' hk hk' _; simp at hk hk'; omega
  | succ t ih =>
    intro k k' hk hk' h
    obtain ⟨a, b⟩ := nodeAt_spec h1 h3 t (k / 2)
    obtain ⟨a', b'⟩ := nodeAt_spec h1 h3 t (k' / 2)
    have hp : nodeAt r t (k / 2) = nodeAt r t (k' / 2) := child_parent_eq a b a' b' h
    rw [Nat.pow_succ] at hk hk'
    have hq : k / 2 = k' / 2 := ih _ _ (by omega) (by omega) hp
    have hb : (k % 2 == 1) = (k' % 2 == 1) := by
      have h' : child (nodeAt r t (k / 2)) (k % 2 == 1) =
          child (nodeAt r t (k / 2)) (k' % 2 == 1) := by
        have := h; simp only [nodeAt] at this; rw [hp] at this ⊢; exact this
      revert h'
      cases (k % 2 == 1) <;> cases (k' % 2 == 1) <;> intro h'
      · rfl
      · exact absurd h' child_ne
      · exact absurd h'.symm child_ne
      · rfl
    have hm : k % 2 = k' % 2 := by
      have a := Nat.mod_two_eq_zero_or_one k
      have b := Nat.mod_two_eq_zero_or_one k'
      rcases a with a | a <;> rcases b with b | b <;> rw [a, b] at hb <;> simp_all
    omega

/-- Ein Gegenbeispiel liefert ein ungerades, das nicht durch 3 teilbar ist. -/
theorem counterexample_odd_not_three : ∀ n, 0 < n → n % 3 ≠ 0 → ¬ ReachesOne n →
    ∃ r, 0 < r ∧ r % 2 = 1 ∧ r % 3 ≠ 0 ∧ ¬ ReachesOne r := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro h0 h3 h
    by_cases h2 : n % 2 = 0
    · have hs : step n = n / 2 := step_even h2
      exact ih (n / 2) (by omega) (by omega) (by omega)
        (fun hr => h (reachesOne_of_step (by rw [hs]; exact hr)))
    · exact ⟨n, h0, by omega, h3, h⟩

/-- **Satz.** Gäbe es ein Gegenbeispiel, dann gäbe es eines `r` (ungerade, `3 ∤ r`) und für jedes
`t` mindestens `2^t` verschiedene Gegenbeispiele `≤ r · 22^t`. -/
theorem many_counterexamples (h : ¬ CollatzConjecture) :
    ∃ r, 0 < r ∧ ∀ t, (∀ k, k < 2 ^ t → nodeAt r t k ≤ r * 22 ^ t ∧ ¬ ReachesOne (nodeAt r t k)) ∧
      (∀ k k', k < 2 ^ t → k' < 2 ^ t → nodeAt r t k = nodeAt r t k' → k = k') := by
  obtain ⟨n, hn, hr⟩ : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact h (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  obtain ⟨n', hn', h3', hr'⟩ := counterexample_not_three n hn hr
  obtain ⟨r, h0, h1, h3, hrr⟩ := counterexample_odd_not_three n' hn' h3' hr'
  refine ⟨r, h0, fun t => ⟨fun k _ => ⟨nodeAt_le h1 h3 t k, fun hk => ?_⟩,
    nodeAt_injective h1 h3 t⟩⟩
  obtain ⟨j, hj⟩ := nodeAt_reaches h1 h3 t k
  exact hrr (hj ▸ reachesOne_iter hk j)

end Collatz
