import Collatz.Krasikov
import Collatz.ManyCounterexamples

/-!
# Satz 47: etwa `x^0.532` Zahlen `≤ x` erreichen die 1

Die Tabelle `qQ 4 10 50` aus `Krasikov.lean` (Buchführung modulo `3^4 = 81`, Exponenten `E ≤ 10`)
wird hier einmal ausgerechnet: In Tiefe 14 mit `S = 50` liegen unter **jedem** ungeraden `n` mit
`3 ∤ n` mindestens `L₀ = 28 687` Knoten `m` mit `3^14·m ≤ 2^50·n`. Diese endliche Rechnung
(`block_value`) ist der einzige Rechenschritt; sie betrifft die Tabelle, nicht einzelne
Collatz-Folgen. Der Block-Satz hängt `k` solche Blöcke aneinander, für **jedes** `k`:

`L₀^k` verschiedene Zahlen `m ≤ 5 · (2^50/3^14)^k`, die alle die 1 erreichen.

Wegen `log L₀ / log(2^50/3^14) ≈ 0.5325` sind das für jedes `x` etwa `x^0.532` Zahlen `≤ x`
(Satz 46: 0.374). Gäbe es ein Gegenbeispiel, so gäbe es ebenso viele Gegenbeispiele.
-/

namespace Collatz

set_option maxRecDepth 100000 in
/-- Die einzige endliche Rechnung: der Wert der Tabelle in Tiefe 14 bei `S = 50`. -/
theorem block_value : ∀ t, t < 27 → t % 3 ≠ 0 → 28687 ≤ qQ 4 10 50 14 t 50 := by
  decide +kernel

theorem block_value' : ∀ t, t < 3 ^ (4 - 1) → t % 3 ≠ 0 → 28687 ≤ qQ 4 10 50 14 t 50 :=
  block_value

/-- **Satz 47.** Für jedes `k` gibt es `28 687^k` verschiedene Zahlen `m` mit
`3^(14k)·m ≤ 5·2^(50k)`, die alle die 1 erreichen. -/
theorem krasikov_reach_one (k : Nat) :
    ∃ L : List Nat, L.Nodup ∧ 28687 ^ k ≤ L.length ∧
      ∀ m ∈ L, 3 ^ (k * 14) * m ≤ 2 ^ (k * 50) * 5 ∧ ReachesOne m := by
  obtain ⟨L, hn, hl, hg⟩ := block (by decide) (tabQ_cert 4 10 50 14) (Nat.le_refl 14)
    (Nat.le_refl 50) block_value' k 5 (by decide) (by decide)
  refine ⟨L, hn, hl, fun m hm => ⟨(hg m hm).2.2.1, ?_⟩⟩
  obtain ⟨j, hj⟩ := (hg m hm).2.2.2.2
  exact ⟨j + 5, by rw [iter_add, hj]; decide⟩

/-- **Gegenbeispiel-Version.** -/
theorem krasikov_counterexamples (h : ¬ CollatzConjecture) :
    ∃ r, 0 < r ∧ ∀ k, ∃ L : List Nat, L.Nodup ∧ 28687 ^ k ≤ L.length ∧
      ∀ m ∈ L, 3 ^ (k * 14) * m ≤ 2 ^ (k * 50) * r ∧ ¬ ReachesOne m := by
  obtain ⟨n, hn, hr⟩ : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact h (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  obtain ⟨n', hn', h3', hr'⟩ := counterexample_not_three n hn hr
  obtain ⟨r, h0, h1, h3, hrr⟩ := counterexample_odd_not_three n' hn' h3' hr'
  refine ⟨r, h0, fun k => ?_⟩
  obtain ⟨L, hnd, hl, hg⟩ := block (by decide) (tabQ_cert 4 10 50 14) (Nat.le_refl 14)
    (Nat.le_refl 50) block_value' k r h1 h3
  refine ⟨L, hnd, hl, fun m hm => ⟨(hg m hm).2.2.1, fun hm' => ?_⟩⟩
  obtain ⟨j, hj⟩ := (hg m hm).2.2.2.2
  exact hrr (hj ▸ reachesOne_iter hm' j)

end Collatz
