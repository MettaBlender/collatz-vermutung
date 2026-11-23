import Collatz.KrasikovB50
import Collatz.ManyCounterexamples

/-!
# Satz 47: etwa `x^0.665` Zahlen `≤ x` erreichen die 1

Die Tabelle `tabQ 5 14 163` aus `Krasikov.lean` (Buchführung modulo `3^5 = 243`, Exponenten
`E ≤ 14`, `S ≤ 163`) wird in zehn Etappen zu je fünf Stufen nachgerechnet (`KrasikovB5` bis
`KrasikovB50`, je `decide +kernel`). Dafür rechnet `KrasikovFast.lean` ganze Zeilen auf einmal
(`fastNext`, bewiesen gleich `nextT`), etwa 25-mal schneller. In Tiefe 50 liegen unter **jedem**
ungeraden `n` mit `3 ∤ n` mindestens `L₀ = 58 525 359 050 790 615` Knoten `m` mit
`3^50·m ≤ 2^163·n`. Diese endlichen Rechnungen betreffen die Tabelle, nicht einzelne
Collatz-Folgen. Der Block-Satz hängt `k` solche Blöcke aneinander, für **jedes** `k`:

`L₀^k` verschiedene Zahlen `m ≤ 5 · (2^163/3^50)^k`, die alle die 1 erreichen.

Wegen `log L₀ / log(2^163/3^50) ≈ 0.6651` sind das für jedes `x` etwa `x^0.665` Zahlen `≤ x`
(Satz 46: 0.374; Krasikov 1989: `x^(3/7)`). Gäbe es ein Gegenbeispiel, so gäbe es ebenso viele.
-/

namespace Collatz

theorem tabFrom_of_fast {L L' : List (List Nat)} (h : fastFrom 5 14 163 L 5 = L') :
    tabFrom 5 14 163 L 5 = L' := (fastFrom_eq 5 14 163 L 5).symm.trans h

/-- Das Zertifikat bis Tiefe 50, zusammengesetzt aus den zehn Etappen. -/
theorem cert50 : ∃ q : Nat → Nat → Nat → Nat, Cert 5 14 50 163 q ∧
    q 50 = getT (tabFrom 5 14 163 Q45 5) := by
  have c0 := tabQ_cert 5 14 163 5
  have h0 : qQ 5 14 163 5 = getT Q5 := by
    have e := tabFrom_of_fast segB5
    rw [tabFrom_tabQ] at e
    funext t S; show getT (tabQ 5 14 163 5) t S = _; rw [← e]
  obtain ⟨q1, c1, h1⟩ := ext_step c0 h0 5 (tabFrom_of_fast segB10)
  obtain ⟨q2, c2, h2⟩ := ext_step c1 h1 5 (tabFrom_of_fast segB15)
  obtain ⟨q3, c3, h3⟩ := ext_step c2 h2 5 (tabFrom_of_fast segB20)
  obtain ⟨q4, c4, h4⟩ := ext_step c3 h3 5 (tabFrom_of_fast segB25)
  obtain ⟨q5, c5, h5⟩ := ext_step c4 h4 5 (tabFrom_of_fast segB30)
  obtain ⟨q6, c6, h6⟩ := ext_step c5 h5 5 (tabFrom_of_fast segB35)
  obtain ⟨q7, c7, h7⟩ := ext_step c6 h6 5 (tabFrom_of_fast segB40)
  obtain ⟨q8, c8, h8⟩ := ext_step c7 h7 5 (tabFrom_of_fast segB45)
  exact ext_step c8 h8 5 rfl

theorem final50 : ∀ t, t < 3 ^ (5 - 1) → t % 3 ≠ 0 →
    58525359050790615 ≤ getT (tabFrom 5 14 163 Q45 5) t 163 := by
  intro t ht h3
  rw [← fastFrom_eq]
  exact allGe_spec segB50 t ht h3

/-- **Satz 47.** Für jedes `k` gibt es `58 525 359 050 790 615^k` verschiedene Zahlen `m` mit
`3^(50k)·m ≤ 5·2^(163k)`, die alle die 1 erreichen. -/
theorem krasikov_reach_one (k : Nat) :
    ∃ L : List Nat, L.Nodup ∧ 58525359050790615 ^ k ≤ L.length ∧
      ∀ m ∈ L, 3 ^ (k * 50) * m ≤ 2 ^ (k * 163) * 5 ∧ ReachesOne m := by
  obtain ⟨q, hc, hq⟩ := cert50
  obtain ⟨L, hn, hl, hg⟩ := block (by decide) hc (Nat.le_refl 50) (Nat.le_refl 163)
    (fun t ht h3 => by rw [hq]; exact final50 t ht h3) k 5 (by decide) (by decide)
  refine ⟨L, hn, hl, fun m hm => ⟨(hg m hm).2.2.1, ?_⟩⟩
  obtain ⟨j, hj⟩ := (hg m hm).2.2.2.2
  exact ⟨j + 5, by rw [iter_add, hj]; decide⟩

/-- **Gegenbeispiel-Version.** -/
theorem krasikov_counterexamples (h : ¬ CollatzConjecture) :
    ∃ r, 0 < r ∧ ∀ k, ∃ L : List Nat, L.Nodup ∧ 58525359050790615 ^ k ≤ L.length ∧
      ∀ m ∈ L, 3 ^ (k * 50) * m ≤ 2 ^ (k * 163) * r ∧ ¬ ReachesOne m := by
  obtain ⟨n, hn, hr⟩ : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact h (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  obtain ⟨n', hn', h3', hr'⟩ := counterexample_not_three n hn hr
  obtain ⟨r, h0, h1, h3, hrr⟩ := counterexample_odd_not_three n' hn' h3' hr'
  refine ⟨r, h0, fun k => ?_⟩
  obtain ⟨q, hc, hq⟩ := cert50
  obtain ⟨L, hnd, hl, hg⟩ := block (by decide) hc (Nat.le_refl 50) (Nat.le_refl 163)
    (fun t ht h3 => by rw [hq]; exact final50 t ht h3) k r h1 h3
  refine ⟨L, hnd, hl, fun m hm => ⟨(hg m hm).2.2.1, fun hm' => ?_⟩⟩
  obtain ⟨j, hj⟩ := (hg m hm).2.2.2.2
  exact hrr (hj ▸ reachesOne_iter hm' j)

end Collatz
