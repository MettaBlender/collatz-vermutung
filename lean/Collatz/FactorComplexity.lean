import Collatz.NoFiniteMemory

/-!
# Satz 61: Eine divergente Bahn hat mindestens `k + 1` verschiedene Fenster der Länge `k`

Ist die Bahn von `n` unbeschränkt, so kommen für jedes `k` und jede Startstelle `m`
mindestens `k + 1` verschiedene Paritätsfenster der Länge `k` an Stellen `≥ m` vor.
(Das ist die untere Schranke von Morse und Hedlund für aperiodische Folgen.) Eine
periodische Folge wie `1,0,1,0,…` hat dagegen für jedes `k` nur 2 Fenster.

Beweis durch Induktion über `k`: Aus `k + 1` verschiedenen Fenstern der Länge `k` macht man
durch Verlängern um eine Parität `k + 1` verschiedene Fenster der Länge `k + 1`. Satz 60
liefert ein Fenster `v` mit zwei verschiedenen Fortsetzungen, und eine davon ist neu.
-/

namespace Collatz

theorem fc_nodup_map {α β : Type} (f : α → β) :
    ∀ L : List α, L.Nodup → (∀ x ∈ L, ∀ y ∈ L, f x = f y → x = y) → (L.map f).Nodup := by
  intro L
  induction L with
  | nil => intro _ _; exact List.nodup_nil
  | cons a L ih =>
    intro hnd hinj
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    constructor
    · intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨b, hb, hfb⟩ := hmem
      have := hinj b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self) hfb
      exact hnd.1 (this ▸ hb)
    · exact ih hnd.2 (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))

/-- Das Fenster `w` der Länge `k` kommt an einer Stelle `≥ m` vor. -/
def fcOcc (n k m : Nat) (w : List Bool) : Prop := ∃ i, m ≤ i ∧ nfmWin k i n = w

/-- **Satz 61**: Für eine unbeschränkte Bahn gibt es zu jedem `k` und `m` eine Liste von
`k + 1` paarweise verschiedenen Fenstern der Länge `k`, die alle an Stellen `≥ m` vorkommen. -/
theorem factor_complexity {n : Nat} (hu : ∀ B, ∃ i, B < Titer i n) (m : Nat) :
    ∀ k, ∃ L : List (List Bool), L.length = k + 1 ∧ L.Nodup ∧ ∀ w ∈ L, fcOcc n k m w := by
  intro k
  induction k with
  | zero =>
    exact ⟨[[]], rfl, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩,
      fun w hw => ⟨m, Nat.le_refl _, by simp at hw; subst hw; rfl⟩⟩
  | succ k ih =>
    obtain ⟨L, hlen, hnd, hocc⟩ := ih
    classical
    let pos : List Bool → Nat := fun w =>
      if h : fcOcc n k m w then Classical.choose h else m
    have hpos : ∀ w, fcOcc n k m w → m ≤ pos w ∧ nfmWin k (pos w) n = w := by
      intro w h
      have := Classical.choose_spec h
      simp only [pos, dif_pos h]; exact this
    let ext : List Bool → List Bool := fun w => nfmWin (k + 1) (pos w) n
    -- jede Fortsetzung hat das alte Fenster als Anfang
    have hext : ∀ w ∈ L, ∃ b, ext w = w ++ [b] := by
      intro w hw
      obtain ⟨_, h2⟩ := hpos w (hocc w hw)
      refine ⟨nthPar (pos w + k) n, ?_⟩
      show nfmWin (k + 1) (pos w) n = _
      rw [(nfm_win_succ k (pos w) n).2, h2]
    have hpre : ∀ w ∈ L, ∀ u b, ext w = u ++ [b] → u.length = k → w = u := by
      intro w hw u b he hl
      obtain ⟨c, hc⟩ := hext w hw
      rw [hc] at he
      have hwl : w.length = k := by
        obtain ⟨_, h2⟩ := hpos w (hocc w hw); rw [← h2, parVec_length]
      exact (List.append_inj he (by rw [hwl, hl])).1
    -- Abschluss, sobald ein neues Fenster `e` gefunden ist
    have finish : ∀ e, fcOcc n (k + 1) m e → (∀ w ∈ L, ext w ≠ e) →
        ∃ L' : List (List Bool), L'.length = k + 1 + 1 ∧ L'.Nodup ∧
          ∀ w ∈ L', fcOcc n (k + 1) m w := by
      intro e he hne
      refine ⟨L.map ext ++ [e], by simp [hlen], ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨fc_nodup_map ext L hnd ?_, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
        · intro x hx y hy hxy
          obtain ⟨c, hc⟩ := hext y hy
          have hyl : y.length = k := by
            obtain ⟨_, h2⟩ := hpos y (hocc y hy); rw [← h2, parVec_length]
          exact hpre x hx y c (hxy.trans hc) hyl
        · intro a ha b hb
          simp at hb; subst hb
          rw [List.mem_map] at ha
          obtain ⟨w, hw, rfl⟩ := ha
          exact hne w hw
      · intro w hw
        rw [List.mem_append, List.mem_map] at hw
        rcases hw with ⟨u, hu', rfl⟩ | hw
        · obtain ⟨h1, _⟩ := hpos u (hocc u hu')
          exact ⟨pos u, h1, rfl⟩
        · simp at hw; subst hw; exact he
    -- Satz 60: ein Fenster v mit zwei verschiedenen Fortsetzungen
    obtain ⟨i, i', hi, hi', hw, hpar⟩ := no_finite_memory hu k m
    let v := nfmWin k i n
    have E1 : nfmWin (k + 1) i n = v ++ [nthPar (i + k) n] := (nfm_win_succ k i n).2
    have E2 : nfmWin (k + 1) i' n = v ++ [nthPar (i' + k) n] := by
      rw [(nfm_win_succ k i' n).2, ← hw]
    have hvl : v.length = k := parVec_length _ _
    have hE12 : nfmWin (k + 1) i n ≠ nfmWin (k + 1) i' n := by
      rw [E1, E2]; intro h
      exact hpar (List.cons.inj (List.append_inj h rfl).2).1
    by_cases hv : v ∈ L
    · by_cases h1 : ext v = nfmWin (k + 1) i n
      · apply finish (nfmWin (k + 1) i' n) ⟨i', hi', rfl⟩
        intro w hwL heq
        have := hpre w hwL v _ (heq.trans E2) hvl
        subst this
        exact hE12 (h1.symm.trans heq)
      · apply finish (nfmWin (k + 1) i n) ⟨i, hi, rfl⟩
        intro w hwL heq
        have := hpre w hwL v _ (heq.trans E1) hvl
        subst this
        exact h1 heq
    · apply finish (nfmWin (k + 1) i n) ⟨i, hi, rfl⟩
      intro w hwL heq
      have := hpre w hwL v _ (heq.trans E1) hvl
      subst this
      exact hv hwL

end Collatz
