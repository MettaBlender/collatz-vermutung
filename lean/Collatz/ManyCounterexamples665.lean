import Collatz.Ancestors
import Collatz.ManyCounterexamples

/-!
# Satz 51: Gäbe es ein Gegenbeispiel, dann etwa `x^0.665` viele

Alle Vorfahren eines Gegenbeispiels sind wieder Gegenbeispiele: Erreichte ein Vorfahr `m`
die 1, so auch jede Zahl auf seiner Bahn, also auch das Gegenbeispiel selbst.
Mit der Vorfahren-Zählung aus Satz 50 hebt das den Exponenten aus Satz 40 von 0.224 auf 0.665:
Gäbe es ein Gegenbeispiel, dann gäbe es eines `n` mit `3 ∤ n`, und für jedes `k` mindestens
`58 525 359 050 790 615^k` verschiedene Gegenbeispiele `m` mit `3^(50k)·m ≤ 2^(163k)·6n`.
-/

namespace Collatz

/-- **Satz 51.** Gäbe es ein Gegenbeispiel, dann gäbe es eines `n` (`3 ∤ n`) und für jedes `k`
mindestens `58 525 359 050 790 615^k` verschiedene Gegenbeispiele `m` mit
`3^(50k)·m ≤ 2^(163k)·6n`, also etwa `(x/6n)^0.665` Gegenbeispiele bis `x`. -/
theorem many_counterexamples_665 (h : ¬ CollatzConjecture) :
    ∃ n, 0 < n ∧ n % 3 ≠ 0 ∧ ∀ k, ∃ L : List Nat, L.Nodup ∧ 58525359050790615 ^ k ≤ L.length ∧
      ∀ m ∈ L, 3 ^ (k * 50) * m ≤ 2 ^ (k * 163) * (6 * n) ∧ ¬ ReachesOne m := by
  obtain ⟨n, hn, hr⟩ : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact h (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  obtain ⟨n', hn', h3', hr'⟩ := counterexample_not_three n hn hr
  refine ⟨n', hn', h3', fun k => ?_⟩
  obtain ⟨L, hnd, hl, hg⟩ := krasikov_ancestors hn' h3' k
  refine ⟨L, hnd, hl, fun m hm => ⟨(hg m hm).1, fun hm1 => ?_⟩⟩
  obtain ⟨j, hj⟩ := (hg m hm).2
  exact hr' (hj ▸ reachesOne_iter hm1 j)

end Collatz
