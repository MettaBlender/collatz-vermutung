import Collatz.KrasikovSeg5
import Collatz.KrasikovSeg10
import Collatz.KrasikovSeg15
import Collatz.KrasikovSeg20
import Collatz.KrasikovSeg25
import Collatz.KrasikovSeg30
import Collatz.ManyCounterexamples

/-!
# Satz 47: etwa `x^0.604` Zahlen `≤ x` erreichen die 1

Die Tabelle `tabQ 4 12 106` aus `Krasikov.lean` (Buchführung modulo `3^4 = 81`, Exponenten
`E ≤ 12`, `S ≤ 106`) wird in sechs Etappen zu je fünf Stufen nachgerechnet
(`KrasikovSeg5` bis `KrasikovSeg30`, je `decide +kernel`). In Tiefe 30 liegen unter **jedem**
ungeraden `n` mit `3 ∤ n` mindestens `L₀ = 42 319 894 058` Knoten `m` mit `3^30·m ≤ 2^106·n`.
Diese endlichen Rechnungen betreffen die Tabelle, nicht einzelne Collatz-Folgen. Der Block-Satz
hängt `k` solche Blöcke aneinander, für **jedes** `k`:

`L₀^k` verschiedene Zahlen `m ≤ 5 · (2^106/3^30)^k`, die alle die 1 erreichen.

Wegen `log L₀ / log(2^106/3^30) ≈ 0.6040` sind das für jedes `x` etwa `x^0.604` Zahlen `≤ x`
(Satz 46: 0.374; Krasikov 1989: `x^(3/7)`). Gäbe es ein Gegenbeispiel, so gäbe es ebenso viele.
-/

namespace Collatz

/-- Das Zertifikat bis Tiefe 30, zusammengesetzt aus den sechs Etappen. -/
theorem cert30 : ∃ q : Nat → Nat → Nat → Nat, Cert 4 12 30 106 q ∧
    q 30 = getT (tabFrom 4 12 106 K25 5) := by
  have c0 := tabQ_cert 4 12 106 5
  have h0 : qQ 4 12 106 5 = getT K5 := by
    funext t S; show getT (tabQ 4 12 106 5) t S = _; rw [seg5]
  obtain ⟨q1, c1, h1⟩ := ext_step c0 h0 5 seg10
  obtain ⟨q2, c2, h2⟩ := ext_step c1 h1 5 seg15
  obtain ⟨q3, c3, h3⟩ := ext_step c2 h2 5 seg20
  obtain ⟨q4, c4, h4⟩ := ext_step c3 h3 5 seg25
  exact ext_step c4 h4 5 rfl

/-- **Satz 47.** Für jedes `k` gibt es `42 319 894 058^k` verschiedene Zahlen `m` mit
`3^(30k)·m ≤ 5·2^(106k)`, die alle die 1 erreichen. -/
theorem krasikov_reach_one (k : Nat) :
    ∃ L : List Nat, L.Nodup ∧ 42319894058 ^ k ≤ L.length ∧
      ∀ m ∈ L, 3 ^ (k * 30) * m ≤ 2 ^ (k * 106) * 5 ∧ ReachesOne m := by
  obtain ⟨q, hc, hq⟩ := cert30
  obtain ⟨L, hn, hl, hg⟩ := block (by decide) hc (Nat.le_refl 30) (Nat.le_refl 106)
    (fun t ht h3 => by rw [hq]; exact seg30 t ht h3) k 5 (by decide) (by decide)
  refine ⟨L, hn, hl, fun m hm => ⟨(hg m hm).2.2.1, ?_⟩⟩
  obtain ⟨j, hj⟩ := (hg m hm).2.2.2.2
  exact ⟨j + 5, by rw [iter_add, hj]; decide⟩

/-- **Gegenbeispiel-Version.** -/
theorem krasikov_counterexamples (h : ¬ CollatzConjecture) :
    ∃ r, 0 < r ∧ ∀ k, ∃ L : List Nat, L.Nodup ∧ 42319894058 ^ k ≤ L.length ∧
      ∀ m ∈ L, 3 ^ (k * 30) * m ≤ 2 ^ (k * 106) * r ∧ ¬ ReachesOne m := by
  obtain ⟨n, hn, hr⟩ : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact h (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  obtain ⟨n', hn', h3', hr'⟩ := counterexample_not_three n hn hr
  obtain ⟨r, h0, h1, h3, hrr⟩ := counterexample_odd_not_three n' hn' h3' hr'
  refine ⟨r, h0, fun k => ?_⟩
  obtain ⟨q, hc, hq⟩ := cert30
  obtain ⟨L, hnd, hl, hg⟩ := block (by decide) hc (Nat.le_refl 30) (Nat.le_refl 106)
    (fun t ht h3 => by rw [hq]; exact seg30 t ht h3) k r h1 h3
  refine ⟨L, hnd, hl, fun m hm => ⟨(hg m hm).2.2.1, fun hm' => ?_⟩⟩
  obtain ⟨j, hj⟩ := (hg m hm).2.2.2.2
  exact hrr (hj ▸ reachesOne_iter hm' j)

end Collatz
