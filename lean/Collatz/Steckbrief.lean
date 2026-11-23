import Collatz.MinClasses
import Collatz.DenseTree
import Collatz.CycleShape27
import Collatz.Dichotomy

/-!
# Steckbrief eines Gegenbeispiels

Fasst zusammen, was ein Gegenbeispiel zur Vermutung alles zugleich erfüllen müsste. Jede Zeile ist
ein bewiesener Satz für **alle** Zahlen; zusammen zeigen sie, wie eng ein Gegenbeispiel eingekreist
ist und warum das trotzdem kein Beweis ist: Keine der Bedingungen ist für sich widersprüchlich.
-/

namespace Collatz

/-- **Steckbrief eines Gegenbeispiels.** Wäre die Vermutung falsch, dann gälte alles zugleich:

1. In **jeder** Restklasse modulo `2^k` gibt es ein Gegenbeispiel (Satz 36).
2. Es gibt ein Gegenbeispiel `m ≥ 2^27`, das kleinstes Glied seiner Folge ist, zu jeder Zeit
   mindestens 63 % ungerade Schritte macht und modulo `2^(1000w)` in einer Klasse vom Anteil
   `≤ 2^(−49w)` liegt (Sätze 27, 32, 37).
3. Es gibt eine unbeschränkte Folge, oder einen Zyklus der Länge `1719a + 38609b` mit
   `a, b ≥ 1` (Satz 13, Satz 27). -/
theorem steckbrief (h : ¬ CollatzConjecture) :
    (∀ k s, ∃ m, 0 < m ∧ m % 2 ^ k = s % 2 ^ k ∧ ¬ ReachesOne m) ∧
    (∃ m, 134217728 ≤ m ∧ IsOrbitMin m ∧ ¬ ReachesOne m ∧
      ∀ w, 630 * w ≤ oddsT (1000 * w) (m % 2 ^ (1000 * w))) ∧
    ((∃ n, 0 < n ∧ ∀ B, ∃ k, B < iter k n) ∨
     (∃ n p a b, 0 < n ∧ Periodic n p ∧ 1 ≤ a ∧ 1 ≤ b ∧ p = 1719 * a + 38609 * b)) := by
  obtain ⟨n, hn, hr⟩ : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact h (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  refine ⟨counterexample_in_every_class h, ?_, ?_⟩
  · obtain ⟨k, hmin, hbig, hw⟩ := counterexample_min_classes hn hr
    exact ⟨iter k n, hbig, hmin, fun h1 => hr (reachesOne_of_iter h1), hw⟩
  · rw [conjecture_iff] at h
    by_cases hb : ∀ n, 0 < n → ∃ B, ∀ k, iter k n ≤ B
    · right
      have hc : ¬ ∀ n p, 0 < n → Periodic n p → n = 1 ∨ n = 4 ∨ n = 2 := fun hc => h ⟨hb, hc⟩
      obtain ⟨n, p, hn, hp, hnt⟩ : ∃ n p, 0 < n ∧ Periodic n p ∧ ¬ (n = 1 ∨ n = 4 ∨ n = 2) := by
        apply Classical.byContradiction
        intro hne
        exact hc (fun n p hn hp => Classical.byContradiction (fun hx => hne ⟨n, p, hn, hp, hx⟩))
      obtain ⟨a, b, ha, hb', _, _, hp'⟩ := cycle_shape27 hp hn (by omega)
      exact ⟨n, p, a, b, hn, hp, ha, hb', hp'⟩
    · left
      obtain ⟨n, hn, hB⟩ : ∃ n, 0 < n ∧ ¬ ∃ B, ∀ k, iter k n ≤ B := by
        apply Classical.byContradiction
        intro hne
        exact hb (fun n hn => Classical.byContradiction (fun hx => hne ⟨n, hn, hx⟩))
      refine ⟨n, hn, fun B => Classical.byContradiction (fun hx => hB ⟨B, fun k => ?_⟩)⟩
      exact Nat.le_of_not_lt (fun hlt => hx ⟨k, hlt⟩)

end Collatz
