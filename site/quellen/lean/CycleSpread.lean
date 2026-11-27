import Collatz.CycleExtremes

/-!
# Satz 72: Spannweite eines Zyklus

Für jeden Zyklus der beschleunigten Abbildung `T` mit Minimum `m` und Maximum `M` gilt

* `M ≥ 2m` (denn der Vorgänger des Minimums ist `2m`, Satz 71), und
* `M = 2m` **nur** für den trivialen Zyklus `1 → 2 → 1`.

Jeder nichttriviale Zyklus hat also ein Glied echt grösser als das Doppelte seines Minimums.

Beweisidee (allgemein, ohne Rechenschranke): Liegt der Zyklus ganz in `[m, 2m]`, so ist `2m`
das einzige gerade Glied (ein gerades `x` mit `x/2 ≥ m` erfüllt `x ≥ 2m`). Ab `m` laufen also
nur ungerade Schritte `x ↦ (3x+1)/2`, für die `2·(x'+1) = 3·(x+1)` gilt. Erreicht die Kette nach
`k ≥ 1` Schritten das gerade Glied `2m`, folgt `2^k (2m+1) = 3^k (m+1)`. Weil `2^k` und `3^k`
teilerfremd sind, ist `m + 1 = 2^k t` und damit `t·(2^(k+1) − 3^k) = 1`. Das geht nur für
`k = 1, t = 1`, also `m = 1`.
-/

namespace Collatz

theorem cs_exists_step (P : Nat → Prop) (N : Nat) (h0 : P 0) (hN : ¬ P N) :
    ∃ k, k < N ∧ P k ∧ ¬ P (k + 1) := by
  induction N with
  | zero => exact absurd h0 hN
  | succ N ih =>
    by_cases hP : P N
    · exact ⟨N, by omega, hP, hN⟩
    · obtain ⟨k, hk, h1, h2⟩ := ih hP
      exact ⟨k, by omega, h1, h2⟩

theorem cs_odd_step (x : Nat) (hx : x % 2 = 1) : 2 * (T x + 1) = 3 * (x + 1) := by
  unfold T; rw [if_neg (by omega)]; omega

theorem cs_pow_gt (k : Nat) (hk : 2 ≤ k) : 2 ^ (k + 1) ≤ 3 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 2 with h | h
    · have : k = 1 := by omega
      subst this; decide
    · have := ih h
      rw [Nat.pow_succ, Nat.pow_succ 3]; omega

/-- Die zahlentheoretische Kernaussage: `2^k (2m+1) = 3^k (m+1)` mit `k ≥ 1` erzwingt `m = 1`. -/
theorem cs_key (k m : Nat) (hk : 1 ≤ k) (h : 2 ^ k * (2 * m + 1) = 3 ^ k * (m + 1)) : m = 1 := by
  have hcop : (2 ^ k).Coprime (3 ^ k) := Nat.Coprime.pow k k (by decide)
  have hd : 2 ^ k ∣ 3 ^ k * (m + 1) := ⟨2 * m + 1, h.symm⟩
  obtain ⟨t, ht⟩ := hcop.dvd_of_dvd_mul_left hd
  have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have h2 : 2 * m + 1 = 3 ^ k * t := by
    rw [ht] at h
    have : 2 ^ k * (2 * m + 1) = 2 ^ k * (3 ^ k * t) := by
      rw [h, ← Nat.mul_assoc, Nat.mul_comm (3 ^ k) (2 ^ k), Nat.mul_assoc]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have h3 : 2 ^ (k + 1) * t = 3 ^ k * t + 1 := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc, ← ht]; omega
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have : k = 1 := by omega
    subst this
    simp at h3 ht; omega
  · have := cs_pow_gt k hk2
    have : 2 ^ (k + 1) * t ≤ 3 ^ k * t := Nat.mul_le_mul_right t this
    omega

/-- **Satz 72.** In jedem Zyklus gibt es ein Glied `≥ 2·Minimum`; liegt der ganze Zyklus in
`[m, 2m]`, so ist `m = 1` (trivialer Zyklus). -/
theorem cycle_spread {n p : Nat} (hp : 0 < p) (h0 : 0 < n) (hc : Titer p n = n) :
    ∃ i, (∀ j, Titer i n ≤ Titer j n) ∧ (∃ j, 2 * Titer i n ≤ Titer j n) ∧
      ((∀ j, Titer j n ≤ 2 * Titer i n) → Titer i n = 1) := by
  obtain ⟨i, _, hmin, hodd, hpred⟩ := cycle_min_odd hp h0 hc
  refine ⟨i, hmin, ⟨i + p - 1, by rw [hpred]; exact Nat.le_refl _⟩, ?_⟩
  intro hmax
  -- a j = Titer (i + j) n
  have hper : Titer (i + p) n = Titer i n := by
    rw [Nat.add_comm, Titer_add, hc]
  let P : Nat → Prop := fun j => (∀ l, l < j → Titer (i + l) n % 2 = 1)
  have chain : ∀ j, P j → 2 ^ j * (Titer (i + j) n + 1) = 3 ^ j * (Titer i n + 1) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hP
      have hPj : P j := fun l hl => hP l (by omega)
      have hoddj := hP j (by omega)
      have e := cs_odd_step _ hoddj
      rw [show i + (j + 1) = (i + j) + 1 by omega, ce_succ, Nat.pow_succ, Nat.pow_succ,
        Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc, Nat.mul_left_comm, e, Nat.mul_left_comm, ih hPj,
        Nat.mul_comm (3 ^ j) 3, Nat.mul_assoc]
  have hP0 : P 0 := fun l hl => absurd hl (Nat.not_lt_zero _)
  have hm0 : 0 < Titer i n := ce_pos h0 i
  have hPp : ¬ P p := by
    intro hP
    have e := chain p hP
    rw [hper] at e
    have h23 : 2 ^ p < 3 ^ p := Nat.pow_lt_pow_left (by decide) (by omega)
    have : 2 ^ p * (Titer i n + 1) < 3 ^ p * (Titer i n + 1) :=
      Nat.mul_lt_mul_of_pos_right h23 (by omega)
    omega
  obtain ⟨k, _, hPk, hPk1⟩ := cs_exists_step P p hP0 hPp
  have hevk : Titer (i + k) n % 2 = 0 := by
    apply Classical.byContradiction
    intro hne
    apply hPk1
    intro l hl
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
    · exact hPk l hl
    · rw [hl]; omega
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp at hevk; omega
    · exact hk
  -- das gerade Glied ist genau 2m
  have hnext := hmin (i + k + 1)
  rw [ce_succ] at hnext
  have hxle := hmax (i + k)
  have hx2 : Titer (i + k) n = 2 * Titer i n := by
    generalize Titer (i + k) n = x at hnext hxle hevk
    unfold T at hnext; rw [if_pos hevk] at hnext; omega
  have e := chain k hPk
  rw [hx2] at e
  exact cs_key k _ hk1 (by rw [show 2 * Titer i n + 1 = 2 * Titer i n + 1 from rfl]; exact e)

/-- Folgerung: Jeder Zyklus mit Minimum `m > 1` hat ein Glied `> 2m`. -/
theorem nontrivial_cycle_exceeds_double {n p : Nat} (hp : 0 < p) (h0 : 0 < n)
    (hc : Titer p n = n) :
    ∃ i, (∀ j, Titer i n ≤ Titer j n) ∧ (Titer i n = 1 ∨ ∃ j, 2 * Titer i n < Titer j n) := by
  obtain ⟨i, hmin, _, h⟩ := cycle_spread hp h0 hc
  refine ⟨i, hmin, ?_⟩
  by_cases hall : ∀ j, Titer j n ≤ 2 * Titer i n
  · exact Or.inl (h hall)
  · right
    apply Classical.byContradiction
    intro hne
    apply hall
    intro j
    apply Classical.byContradiction
    intro hj
    exact hne ⟨j, by omega⟩

end Collatz
