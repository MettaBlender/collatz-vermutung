import Collatz.AncestorGaps

/-!
# Satz 54: Vorfahren in jedem Intervall `[y, 2y)`, und zwar viele

Satz 50 zählt die Vorfahren von `n` **bis** `x`. Sie könnten sich dort aber ungleichmässig
verteilen. Dieser Satz macht die Zählung lokal: Jeder ungerade Vorfahre `m < y` lässt sich
verdoppeln, bis er in `[y, 2y)` liegt, und `2^j · m` ist wieder ein Vorfahre. Verschiedene
ungerade `m` geben verschiedene Zahlen (der ungerade Anteil ist eindeutig). Also enthält
**jedes** Intervall `[y, 2y)` mindestens so viele Vorfahren wie es ungerade Vorfahren unter `y`
gibt, nach Satz 50 also etwa `(y/6n)^0.665`.
-/

namespace Collatz

/-- Verdoppeln, bis die Zahl mindestens `y` ist. -/
def liftTo (y : Nat) : Nat → Nat → Nat
  | 0, m => m
  | f + 1, m => if m < y then liftTo y f (2 * m) else m

theorem liftTo_pow (y : Nat) : ∀ f m, ∃ j, liftTo y f m = 2 ^ j * m := by
  intro f
  induction f with
  | zero => intro m; exact ⟨0, by simp [liftTo]⟩
  | succ f ih =>
    intro m
    simp only [liftTo]
    split
    · obtain ⟨j, hj⟩ := ih (2 * m)
      exact ⟨j + 1, by rw [hj, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2 m]⟩
    · exact ⟨0, by simp⟩

theorem liftTo_lt (y : Nat) : ∀ f m, m < 2 * y → liftTo y f m < 2 * y := by
  intro f
  induction f with
  | zero => intro m h; simpa [liftTo] using h
  | succ f ih =>
    intro m h
    simp only [liftTo]
    split
    · exact ih _ (by omega)
    · exact h

theorem liftTo_ge (y : Nat) : ∀ f m, 0 < m → y ≤ f + m → y ≤ liftTo y f m := by
  intro f
  induction f with
  | zero => intro m _ h; simpa [liftTo] using h
  | succ f ih =>
    intro m h0 h
    simp only [liftTo]
    split
    · exact ih _ (by omega) (by omega)
    · omega

/-- Kleines Hilfslemma: `map` erhält `Nodup`, wenn die Funktion auf der Liste injektiv ist. -/
theorem nodup_map_of_inj {f : Nat → Nat} : ∀ {L : List Nat}, L.Nodup →
    (∀ a ∈ L, ∀ b ∈ L, f a = f b → a = b) → (L.map f).Nodup := by
  intro L
  induction L with
  | nil => intro _ _; exact List.nodup_nil
  | cons a L ih =>
    intro hn hinj
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, ih hn.2 (fun x hx z hz => hinj x (by simp [hx]) z (by simp [hz]))⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
    have := hinj b (by simp [hb]) a (by simp) hfb
    exact hn.1 (this ▸ hb)

/-- **Satz 54.** Ist `3 ∤ n`, so enthält für jedes `k` jedes Intervall `[y, 2y)` mit
`2^(163k)·6n ≤ 3^(50k)·y` mindestens `58 525 359 050 790 615^k` verschiedene Vorfahren von `n`. -/
theorem ancestors_in_dyadic {n : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) (k y : Nat)
    (hy : 2 ^ (k * 163) * (6 * n) ≤ 3 ^ (k * 50) * y) :
    ∃ L : List Nat, L.Nodup ∧ 58525359050790615 ^ k ≤ L.length ∧
      ∀ x ∈ L, y ≤ x ∧ x < 2 * y ∧ ∃ j, iter j x = n := by
  obtain ⟨c, i, hc1, hc3, hcn, hci⟩ := odd_ancestor h0 h3
  obtain ⟨q, hc, hq⟩ := cert50
  obtain ⟨L, hn, hl, hg⟩ := block (by decide) hc (Nat.le_refl 50) (Nat.le_refl 163)
    (fun t ht h3 => by rw [hq]; exact final50 t ht h3) k c hc1 hc3
  have h3pos : 0 < 3 ^ (k * 50) := Nat.pow_pos (by decide)
  -- jedes m in L ist ungerade, positiv und ≤ y
  have hmy : ∀ m ∈ L, m % 2 = 1 ∧ m ≤ y := by
    intro m hm
    obtain ⟨h1, _, hle, _, _⟩ := hg m hm
    refine ⟨h1, ?_⟩
    have h1' : 3 ^ (k * 50) * m ≤ 3 ^ (k * 50) * y :=
      Nat.le_trans hle (Nat.le_trans (Nat.mul_le_mul_left _ hcn) hy)
    exact Nat.le_of_mul_le_mul_left h1' h3pos
  refine ⟨L.map (liftTo y y), nodup_map_of_inj hn ?_, by rw [List.length_map]; exact hl, ?_⟩
  · intro a ha b hb hab
    obtain ⟨ja, hja⟩ := liftTo_pow y y a
    obtain ⟨jb, hjb⟩ := liftTo_pow y y b
    rw [hja, hjb] at hab
    exact odd_part_unique ja jb a b (hmy a ha).1 (hmy b hb).1 hab
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hm1, hmy'⟩ := hmy m hm
    refine ⟨liftTo_ge y y m (by omega) (by omega), liftTo_lt y y m (by omega), ?_⟩
    obtain ⟨j, hj⟩ := liftTo_pow y y m
    obtain ⟨i', hi'⟩ := (hg m hm).2.2.2.2
    refine ⟨j + i' + i, ?_⟩
    rw [hj, iter_add, iter_add, iter_two_pow_mul, hi', hci]

/-- Gäbe es ein Gegenbeispiel, dann gäbe es ein `n`, so dass für jedes `k` jedes Intervall
`[y, 2y)` mit `2^(163k)·6n ≤ 3^(50k)·y` mindestens `58 525 359 050 790 615^k` Gegenbeispiele
enthält. -/
theorem counterexamples_in_dyadic (h : ¬ CollatzConjecture) :
    ∃ n, 0 < n ∧ ∀ k y, 2 ^ (k * 163) * (6 * n) ≤ 3 ^ (k * 50) * y →
      ∃ L : List Nat, L.Nodup ∧ 58525359050790615 ^ k ≤ L.length ∧
        ∀ x ∈ L, y ≤ x ∧ x < 2 * y ∧ ¬ ReachesOne x := by
  obtain ⟨n, hn, hr⟩ : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact h (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  obtain ⟨n', hn', h3', hr'⟩ := counterexample_not_three n hn hr
  refine ⟨n', hn', fun k y hy => ?_⟩
  obtain ⟨L, hnd, hl, hg⟩ := ancestors_in_dyadic hn' h3' k y hy
  refine ⟨L, hnd, hl, fun x hx => ⟨(hg x hx).1, (hg x hx).2.1, fun hx1 => ?_⟩⟩
  obtain ⟨j, hj⟩ := (hg x hx).2.2
  exact hr' (hj ▸ reachesOne_iter hx1 j)

end Collatz
