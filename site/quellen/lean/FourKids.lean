import Collatz.Weighted

/-!
# Vier Kinder pro Knoten: Exponent 0.374

Ist `c` ein ungerader Vorfahre von `n` mit `3c + 1 = 2^E · n`, so ist auch `64c + 21` einer:
`3(64c + 21) + 1 = 64 · (3c + 1) = 2^(E+6) · n`, und `64c + 21 ≡ c (mod 3)`. Jeder Knoten des
Baums aus Satz 34 bekommt so vier verschiedene Kinder `kid n b h` (`b` wählt das Kind aus Satz 34,
`h` wählt, ob `c ↦ 64c + 21` angewandt wird), mit

`kid n b h < (6 oder 22) · (1 oder 64) · n`.

Ein Weg der Länge `t` wird durch zwei Zahlen `k₁, k₂ < 2^t` codiert. Hat `k₁` genau `a` Nullbits
und `k₂` genau `h` Nullbits, so ist der Knoten `≤ r · 6^a · 22^(t−a) · 64^h`, und es gibt
`C(t,a) · C(t,h)` solche Paare.

**Satz** (`four_kids_reach_one`): Für alle `t, a, h` gibt es `C(t,a)·C(t,h)` verschiedene Zahlen
`≤ 5 · 6^a · 22^(t−a) · 64^h`, die die 1 erreichen. Optimiert ergibt das etwa `x^α` Zahlen `≤ x`
mit `(6^(−α) + 22^(−α)) · (1 + 64^(−α)) = 1`, also `α ≈ 0.374` (Satz 45: 0.291, Satz 34: 0.224).
Die Gegenbeispiel-Version gilt ebenso.
-/

namespace Collatz

/-- Optional `c ↦ 64c + 21`. -/
def G (h : Bool) (c : Nat) : Nat := if h then 64 * c + 21 else c

/-- Die vier Kinder. -/
def kid (n : Nat) (b h : Bool) : Nat := G h (child n b)

theorem kid_spec {n : Nat} (h1 : n % 2 = 1) (h3 : n % 3 ≠ 0) (b h : Bool) :
    kid n b h % 2 = 1 ∧ kid n b h % 3 ≠ 0 ∧ ∃ E, 3 * kid n b h + 1 = 2 ^ E * n := by
  obtain ⟨c1, c3, E, _, hE⟩ := child_spec h1 h3 b
  unfold kid G
  generalize child n b = c at c1 c3 hE
  cases h with
  | false => exact ⟨c1, c3, E, hE⟩
  | true =>
    simp only [if_true]
    refine ⟨by omega, by omega, E + 6, ?_⟩
    rw [Nat.pow_add]
    have : (2 : Nat) ^ 6 = 64 := rfl
    rw [this]
    have e : 3 * (64 * c + 21) + 1 = 64 * (3 * c + 1) := by omega
    rw [e, hE]; grind

theorem kid_reaches {n : Nat} (h1 : n % 2 = 1) (h3 : n % 3 ≠ 0) (b h : Bool) :
    ∃ j, iter j (kid n b h) = n := by
  obtain ⟨hc, _, E, hE⟩ := kid_spec h1 h3 b h
  refine ⟨1 + E, ?_⟩
  rw [iter_add]
  have : iter 1 (kid n b h) = 2 ^ E * n := by
    show step (kid n b h) = 2 ^ E * n
    rw [step_odd hc, hE]
  rw [this, iter_double_pow]

/-- Grösse: `kid n b h < f(b) · g(h) · n` mit `f = 6, 22` und `g = 1, 64`. -/
theorem kid_lt {n : Nat} (h1 : n % 2 = 1) (h3 : n % 3 ≠ 0) (b h : Bool) :
    kid n b h < (if b then 22 else 6) * (if h then 64 else 1) * n := by
  have hf : child n b < (if b then 22 else 6) * n := by
    cases b with
    | false => exact child_false_lt h1 h3
    | true => exact child_lt h1 h3 true
  unfold kid G
  generalize child n b = c at hf
  generalize (if b then 22 else 6) = f at hf
  cases h with
  | false => simpa using hf
  | true =>
    simp only [if_true]
    have : 64 * (c + 1) ≤ 64 * (f * n) := Nat.mul_le_mul_left 64 hf
    have e : f * 64 * n = 64 * (f * n) := by grind
    omega

/-- Gleiche Kinder haben gleiche Eltern. -/
theorem kid_parent_eq {n m : Nat} (hn1 : n % 2 = 1) (hn3 : n % 3 ≠ 0) (hm1 : m % 2 = 1)
    (hm3 : m % 3 ≠ 0) {b h b' h' : Bool} (e : kid n b h = kid m b' h') : n = m := by
  obtain ⟨_, _, E, hE⟩ := kid_spec hn1 hn3 b h
  obtain ⟨_, _, E', hE'⟩ := kid_spec hm1 hm3 b' h'
  rw [e] at hE
  exact odd_part_unique E E' n m hn1 hm1 (by omega)

/-- Die vier Kinder sind verschieden. -/
theorem kid_inj {n : Nat} {b h b' h' : Bool} (e : kid n b h = kid n b' h') : b = b' ∧ h = h' := by
  revert e
  unfold kid G child
  generalize firstAnc n = c
  cases b <;> cases h <;> cases b' <;> cases h' <;>
    simp only [Bool.false_eq_true, if_false, if_true, and_self, true_and, and_true] <;>
    (intro e; first | trivial | (split at e <;> split at e <;> omega) |
      (split at e <;> omega) | (revert e; split <;> split <;> omega) | (revert e; split <;> omega))

/-- Der Viererbaum über der Wurzel `r`, Wege codiert durch zwei Zahlen. -/
def node4 (r : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => r
  | t + 1, k, l => kid (node4 r t (k / 2) (l / 2)) (k % 2 == 1) (l % 2 == 0)

theorem node4_spec {r : Nat} (h1 : r % 2 = 1) (h3 : r % 3 ≠ 0) :
    ∀ t k l, node4 r t k l % 2 = 1 ∧ node4 r t k l % 3 ≠ 0 := by
  intro t
  induction t with
  | zero => intro k l; exact ⟨h1, h3⟩
  | succ t ih =>
    intro k l
    obtain ⟨a, b⟩ := ih (k / 2) (l / 2)
    obtain ⟨c1, c3, _⟩ := kid_spec a b (k % 2 == 1) (l % 2 == 0)
    exact ⟨c1, c3⟩

theorem node4_reaches {r : Nat} (h1 : r % 2 = 1) (h3 : r % 3 ≠ 0) :
    ∀ t k l, ∃ j, iter j (node4 r t k l) = r := by
  intro t
  induction t with
  | zero => intro k l; exact ⟨0, rfl⟩
  | succ t ih =>
    intro k l
    obtain ⟨a, b⟩ := node4_spec h1 h3 t (k / 2) (l / 2)
    obtain ⟨j, hj⟩ := kid_reaches a b (k % 2 == 1) (l % 2 == 0)
    obtain ⟨i, hi⟩ := ih (k / 2) (l / 2)
    exact ⟨j + i, by
      show iter (j + i) (kid (node4 r t (k / 2) (l / 2)) (k % 2 == 1) (l % 2 == 0)) = r
      rw [iter_add, hj, hi]⟩

theorem node4_le {r : Nat} (h1 : r % 2 = 1) (h3 : r % 3 ≠ 0) :
    ∀ t k l, node4 r t k l ≤ r * 6 ^ zeros t k * 22 ^ (t - zeros t k) * 64 ^ zeros t l := by
  intro t
  induction t with
  | zero => intro k l; simp [node4, zeros]
  | succ t ih =>
    intro k l
    obtain ⟨a, b⟩ := node4_spec h1 h3 t (k / 2) (l / 2)
    have hz := zeros_le t (k / 2)
    have hi := ih (k / 2) (l / 2)
    have hk := kid_lt a b (k % 2 == 1) (l % 2 == 0)
    show kid (node4 r t (k / 2) (l / 2)) (k % 2 == 1) (l % 2 == 0) ≤
      r * 6 ^ (zeros t (k / 2) + (if k % 2 = 1 then 0 else 1)) *
        22 ^ (t + 1 - (zeros t (k / 2) + (if k % 2 = 1 then 0 else 1))) *
        64 ^ (zeros t (l / 2) + (if l % 2 = 1 then 0 else 1))
    generalize kid (node4 r t (k / 2) (l / 2)) (k % 2 == 1) (l % 2 == 0) = x at hk
    generalize node4 r t (k / 2) (l / 2) = y at hi hk
    generalize zeros t (k / 2) = z at hz hi
    generalize zeros t (l / 2) = w at hi
    by_cases hk1 : k % 2 = 1 <;> by_cases hl1 : l % 2 = 1
    · have bk : (k % 2 == 1) = true := by simp [hk1]
      have bl : (l % 2 == 0) = false := by simp [hl1]
      rw [bk, bl] at hk; rw [if_pos hk1, if_pos hl1]
      simp only [if_true, Bool.false_eq_true, if_false, Nat.add_zero] at hk ⊢
      have := Nat.lt_of_lt_of_le hk (Nat.mul_le_mul_left _ hi)
      have e : t + 1 - z = (t - z) + 1 := by omega
      rw [e, Nat.pow_succ]
      have : 22 * 1 * (r * 6 ^ z * 22 ^ (t - z) * 64 ^ w) = r * 6 ^ z * (22 ^ (t - z) * 22) * 64 ^ w := by grind
      omega
    · have bk : (k % 2 == 1) = true := by simp [hk1]
      have bl : (l % 2 == 0) = true := by simp; omega
      rw [bk, bl] at hk; rw [if_pos hk1, if_neg hl1]
      simp only [if_true, Nat.add_zero] at hk ⊢
      have := Nat.lt_of_lt_of_le hk (Nat.mul_le_mul_left _ hi)
      have e : t + 1 - z = (t - z) + 1 := by omega
      rw [e, Nat.pow_succ, Nat.pow_succ 64]
      have : 22 * 64 * (r * 6 ^ z * 22 ^ (t - z) * 64 ^ w) = r * 6 ^ z * (22 ^ (t - z) * 22) * (64 ^ w * 64) := by grind
      omega
    · have bk : (k % 2 == 1) = false := by simp [hk1]
      have bl : (l % 2 == 0) = false := by simp [hl1]
      rw [bk, bl] at hk; rw [if_neg hk1, if_pos hl1]
      simp only [Bool.false_eq_true, if_false, Nat.add_zero] at hk ⊢
      have := Nat.lt_of_lt_of_le hk (Nat.mul_le_mul_left _ hi)
      have e : t + 1 - (z + 1) = t - z := by omega
      rw [e, Nat.pow_succ]
      have : 6 * 1 * (r * 6 ^ z * 22 ^ (t - z) * 64 ^ w) = r * (6 ^ z * 6) * 22 ^ (t - z) * 64 ^ w := by grind
      omega
    · have bk : (k % 2 == 1) = false := by simp [hk1]
      have bl : (l % 2 == 0) = true := by simp; omega
      rw [bk, bl] at hk; rw [if_neg hk1, if_neg hl1]
      simp only [Bool.false_eq_true, if_false, if_true] at hk ⊢
      have := Nat.lt_of_lt_of_le hk (Nat.mul_le_mul_left _ hi)
      have e : t + 1 - (z + 1) = t - z := by omega
      rw [e, Nat.pow_succ, Nat.pow_succ 64]
      have : 6 * 64 * (r * 6 ^ z * 22 ^ (t - z) * 64 ^ w) = r * (6 ^ z * 6) * 22 ^ (t - z) * (64 ^ w * 64) := by grind
      omega

theorem node4_injective {r : Nat} (h1 : r % 2 = 1) (h3 : r % 3 ≠ 0) :
    ∀ t k l k' l', k < 2 ^ t → l < 2 ^ t → k' < 2 ^ t → l' < 2 ^ t →
      node4 r t k l = node4 r t k' l' → k = k' ∧ l = l' := by
  intro t
  induction t with
  | zero => intro k l k' l' hk hl hk' hl' _; simp at hk hl hk' hl'; omega
  | succ t ih =>
    intro k l k' l' hk hl hk' hl' e
    obtain ⟨a, b⟩ := node4_spec h1 h3 t (k / 2) (l / 2)
    obtain ⟨a', b'⟩ := node4_spec h1 h3 t (k' / 2) (l' / 2)
    have hp : node4 r t (k / 2) (l / 2) = node4 r t (k' / 2) (l' / 2) := kid_parent_eq a b a' b' e
    rw [Nat.pow_succ] at hk hl hk' hl'
    obtain ⟨q1, q2⟩ := ih _ _ _ _ (by omega) (by omega) (by omega) (by omega) hp
    have e' : kid (node4 r t (k / 2) (l / 2)) (k % 2 == 1) (l % 2 == 0) =
        kid (node4 r t (k / 2) (l / 2)) (k' % 2 == 1) (l' % 2 == 0) := by
      have := e; simp only [node4] at this; rw [hp] at this ⊢; exact this
    obtain ⟨hb, hh⟩ := kid_inj e'
    have m1 : k % 2 = k' % 2 := by
      rcases Nat.mod_two_eq_zero_or_one k with x | x <;>
        rcases Nat.mod_two_eq_zero_or_one k' with y | y <;> rw [x, y] at hb <;>
        first | omega | exact absurd hb (by decide)
    have m2 : l % 2 = l' % 2 := by
      rcases Nat.mod_two_eq_zero_or_one l with x | x <;>
        rcases Nat.mod_two_eq_zero_or_one l' with y | y <;> rw [x, y] at hh <;>
        first | omega | exact absurd hh (by decide)
    omega

/-- **Satz (vier Kinder, für alle `t, a, h`).** Die Paare `(k, l)` mit `k, l < 2^t`,
`zeros t k = a`, `zeros t l = h` (davon gibt es `C(t,a)` mal `C(t,h)`) liefern verschiedene Zahlen
`≤ 5·6^a·22^(t−a)·64^h`, die alle die 1 erreichen. -/
theorem four_kids_reach_one (t a h : Nat) :
    countBelow (fun k => decide (zeros t k = a)) (2 ^ t) = binom t a ∧
    countBelow (fun l => decide (zeros t l = h)) (2 ^ t) = binom t h ∧
    (∀ k l, k < 2 ^ t → l < 2 ^ t → zeros t k = a → zeros t l = h →
      node4 5 t k l ≤ 5 * 6 ^ a * 22 ^ (t - a) * 64 ^ h ∧ ReachesOne (node4 5 t k l)) ∧
    (∀ k l k' l', k < 2 ^ t → l < 2 ^ t → k' < 2 ^ t → l' < 2 ^ t →
      node4 5 t k l = node4 5 t k' l' → k = k' ∧ l = l') := by
  have h1 : (5 : Nat) % 2 = 1 := by decide
  have h3 : (5 : Nat) % 3 ≠ 0 := by decide
  refine ⟨count_zeros t a, count_zeros t h, fun k l _ _ ha hh => ⟨?_, ?_⟩, node4_injective h1 h3 t⟩
  · have := node4_le h1 h3 t k l; rwa [ha, hh] at this
  · obtain ⟨j, hj⟩ := node4_reaches h1 h3 t k l
    exact ⟨5 + j, by rw [Nat.add_comm, iter_add, hj]; decide⟩

/-- **Gegenbeispiel-Version.** -/
theorem four_kids_counterexamples (hc : ¬ CollatzConjecture) :
    ∃ r, r % 2 = 1 ∧ r % 3 ≠ 0 ∧ ∀ t a h,
      (∀ k l, k < 2 ^ t → l < 2 ^ t → zeros t k = a → zeros t l = h →
        node4 r t k l ≤ r * 6 ^ a * 22 ^ (t - a) * 64 ^ h ∧ ¬ ReachesOne (node4 r t k l)) ∧
      (∀ k l k' l', k < 2 ^ t → l < 2 ^ t → k' < 2 ^ t → l' < 2 ^ t →
        node4 r t k l = node4 r t k' l' → k = k' ∧ l = l') := by
  obtain ⟨n, hn, hr⟩ : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact hc (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  obtain ⟨n', hn', h3', hr'⟩ := counterexample_not_three n hn hr
  obtain ⟨r, _, h1, h3, hrr⟩ := counterexample_odd_not_three n' hn' h3' hr'
  refine ⟨r, h1, h3, fun t a h => ⟨fun k l _ _ ha hh => ⟨?_, ?_⟩, node4_injective h1 h3 t⟩⟩
  · have := node4_le h1 h3 t k l; rwa [ha, hh] at this
  · intro hk
    obtain ⟨j, hj⟩ := node4_reaches h1 h3 t k l
    exact hrr (hj ▸ reachesOne_iter hk j)

end Collatz
