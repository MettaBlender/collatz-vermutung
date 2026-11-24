import Collatz.ManyCounterexamples665
import Collatz.ModThree

/-!
# Satz 52: Jeder Zyklus hat ein Einzugsgebiet der Grösse `x^0.665`

Ein Zyklus enthält kein Vielfaches von 3 (`periodic_not_mul_three`). Darum hat nach Satz 50
jedes Zyklusglied `n` für jedes `k` mindestens `58 525 359 050 790 615^k` verschiedene
Vorfahren `m ≤ 6n·(2^163/3^50)^k`. Für den Zyklus 1 → 4 → 2 → 1 ist das wieder Satz 47.

Ist der Zyklus nichttrivial, so sind alle diese Vorfahren Gegenbeispiele: Erreichte einer die 1,
dann auch das Zyklusglied, und ein Zyklus durch die 1 ist der triviale.

Ebenso hat jede Bahn ab einem Punkt nur noch Glieder `3 ∤ iter i n`
(`eventually_not_mul_three`), also hat auch jede divergente Bahn ab dort lauter Glieder
mit Einzugsgebiet `x^0.665`.
-/

namespace Collatz

/-- **Satz 52.** Jedes Glied `n` eines Zyklus hat für jedes `k` mindestens
`58 525 359 050 790 615^k` verschiedene Vorfahren `m` mit `3^(50k)·m ≤ 2^(163k)·6n`. -/
theorem cycle_basin {n p : Nat} (hp : Periodic n p) (h0 : 0 < n) (k : Nat) :
    ∃ L : List Nat, L.Nodup ∧ 58525359050790615 ^ k ≤ L.length ∧
      ∀ m ∈ L, 3 ^ (k * 50) * m ≤ 2 ^ (k * 163) * (6 * n) ∧ ∃ j, iter j m = n :=
  krasikov_ancestors h0 (periodic_not_mul_three hp h0) k

/-- Für einen nichttrivialen Zyklus sind alle diese Vorfahren Gegenbeispiele. -/
theorem nontrivial_cycle_basin {n p : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) (k : Nat) :
    ∃ L : List Nat, L.Nodup ∧ 58525359050790615 ^ k ≤ L.length ∧
      ∀ m ∈ L, 3 ^ (k * 50) * m ≤ 2 ^ (k * 163) * (6 * n) ∧ ¬ ReachesOne m := by
  obtain ⟨L, hnd, hl, hg⟩ := cycle_basin hp h0 k
  refine ⟨L, hnd, hl, fun m hm => ⟨(hg m hm).1, fun hm1 => ?_⟩⟩
  obtain ⟨j, hj⟩ := (hg m hm).2
  have hr : ReachesOne n := hj ▸ reachesOne_iter hm1 j
  rcases periodic_reachesOne hp hr with h | h | h <;> omega

end Collatz
