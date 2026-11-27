import Collatz.CycleSpread

/-!
# Satz 73: Die Steiner-Form der 1-Zyklen

Ein **1-Zyklus** (Steiner 1977) startet in einem ungeraden `m`, macht `o ≥ 1` ungerade Schritte
`x ↦ (3x+1)/2` am Stück und landet bei `2^e · m`; danach führen `e` Halbierungen zurück zu `m`.

Für **alle** `o` und `e` (ohne Rechenschranke) zeigen wir:

* Die Kette schliesst sich wirklich: `Titer (o + e) m = m`.
* `m + 1 = 2^o · t` für ein `t ≥ 1`, und `2^(o+e) · t + 1 = 3^o · t + 2^e`,
  also `t · (2^(o+e) − 3^o) = 2^e − 1`.
* Folgerungen: `3^o < 2^(o+e)`, damit `o < 2e`; ausserdem `2^o − 1 ≤ m < 2^(o+e)`.
* Für `e ≤ 3` gibt es nur den trivialen Zyklus `1 → 2 → 1` (`m = 1`, `o = e = 1`), für **jedes** `o`.

Steiner hat mit Baker-Theorie gezeigt, dass es gar keinen nichttrivialen 1-Zyklus gibt. Die
Gleichung `t · (2^(o+e) − 3^o) = 2^e − 1` ist der elementare Kern davon; für festes `e` lässt sie
wegen `o < 2e` nur endlich viele `o` zu.
-/

namespace Collatz

theorem st_halve (m : Nat) : ∀ e, Titer e (2 ^ e * m) = m := by
  intro e
  induction e with
  | zero => simp [Titer]
  | succ e ih =>
    show Titer e (T (2 ^ (e + 1) * m)) = m
    have : T (2 ^ (e + 1) * m) = 2 ^ e * m := by
      unfold T
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ e) 2, Nat.mul_assoc, if_pos (by omega)]
      omega
    rw [this, ih]

theorem st_chain (m o : Nat) (hodd : ∀ j, j < o → Titer j m % 2 = 1) :
    ∀ j, j ≤ o → 2 ^ j * (Titer j m + 1) = 3 ^ j * (m + 1) := by
  intro j
  induction j with
  | zero => intro _; simp [Titer]
  | succ j ih =>
    intro hj
    have e := cs_odd_step _ (hodd j (by omega))
    rw [ce_succ, Nat.pow_succ, Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc,
      Nat.mul_left_comm, e, Nat.mul_left_comm, ih (by omega), Nat.mul_comm (3 ^ j) 3,
      Nat.mul_assoc]

theorem st_pow_ge (o e : Nat) (h : 2 * e ≤ o) : 2 ^ (o + e) ≤ 3 ^ o := by
  induction o with
  | zero => have : e = 0 := by omega
            subst this; decide
  | succ o ih =>
    rcases Nat.lt_or_ge o (2 * e) with h' | h'
    · have ho : o + 1 = 2 * e := by omega
      rw [ho, show 2 * e + e = 3 * e by omega, Nat.pow_mul, Nat.pow_mul]
      exact Nat.pow_le_pow_left (by decide) e
    · have := ih h'
      rw [show o + 1 + e = (o + e) + 1 by omega, Nat.pow_succ, Nat.pow_succ 3]
      omega

/-- **Satz 73 (Steiner-Form).** -/
theorem steiner_shape (m o e : Nat) (_hm : 0 < m) (_ho : 1 ≤ o)
    (hodd : ∀ j, j < o → Titer j m % 2 = 1) (hk : Titer o m = 2 ^ e * m) :
    Titer (o + e) m = m ∧
    ∃ t, 1 ≤ t ∧ m + 1 = 2 ^ o * t ∧ 2 ^ (o + e) * t + 1 = 3 ^ o * t + 2 ^ e := by
  refine ⟨by rw [Titer_add, hk, st_halve], ?_⟩
  have h := st_chain m o hodd o (Nat.le_refl _)
  rw [hk] at h
  have hcop : (2 ^ o).Coprime (3 ^ o) := Nat.Coprime.pow o o (by decide)
  obtain ⟨t, ht⟩ := hcop.dvd_of_dvd_mul_left ⟨2 ^ e * m + 1, h.symm⟩
  have hpos : 0 < 2 ^ o := Nat.pow_pos (by decide)
  have h2 : 2 ^ e * m + 1 = 3 ^ o * t := by
    rw [ht] at h
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h, ← Nat.mul_assoc, Nat.mul_comm (3 ^ o) (2 ^ o), Nat.mul_assoc]
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; simp at ht
    · exact h0
  refine ⟨t, ht1, ht, ?_⟩
  -- 2^e (m+1) = 2^e 2^o t,  2^e m + 1 = 3^o t
  have h3 : 2 ^ e * (m + 1) = 2 ^ (o + e) * t := by
    rw [ht, Nat.pow_add, ← Nat.mul_assoc, Nat.mul_comm (2 ^ e) (2 ^ o)]
  rw [Nat.mul_add, Nat.mul_one] at h3
  omega

/-- Folgerungen: `3^o < 2^(o+e)`, `o < 2e`, `2^o ≤ m + 1` und `m < 2^(o+e)`. -/
theorem steiner_bounds (m o e : Nat) (hm : 0 < m) (ho : 1 ≤ o)
    (hodd : ∀ j, j < o → Titer j m % 2 = 1) (hk : Titer o m = 2 ^ e * m) :
    3 ^ o < 2 ^ (o + e) ∧ o < 2 * e ∧ 2 ^ o ≤ m + 1 ∧ m < 2 ^ (o + e) := by
  obtain ⟨_, t, ht1, ht, heq⟩ := steiner_shape m o e hm ho hodd hk
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · subst h0
      simp at heq
      have : 2 ^ o < 3 ^ o := Nat.pow_lt_pow_left (by decide) (by omega)
      have : 2 ^ o * t < 3 ^ o * t := Nat.mul_lt_mul_of_pos_right this ht1
      omega
    · exact h0
  have h2e : 2 ≤ 2 ^ e := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) he; simpa using this
  have hlt : 3 ^ o < 2 ^ (o + e) := by
    apply Classical.byContradiction
    intro hn
    have : 2 ^ (o + e) * t ≤ 3 ^ o * t := Nat.mul_le_mul_right t (by omega)
    omega
  refine ⟨hlt, ?_, ?_, ?_⟩
  · apply Classical.byContradiction
    intro hn
    have := st_pow_ge o e (by omega)
    omega
  · rw [ht]; exact Nat.le_mul_of_pos_right _ ht1
  · -- t ≤ 2^e − 1 wegen t·(2^(o+e) − 3^o) = 2^e − 1 und 2^(o+e) − 3^o ≥ 1
    have hd : 3 ^ o * t + t ≤ 2 ^ (o + e) * t := by
      have : (3 ^ o + 1) * t ≤ 2 ^ (o + e) * t := Nat.mul_le_mul_right t (by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; exact this
    have htle : t < 2 ^ e := by omega
    have : 2 ^ o * t < 2 ^ o * 2 ^ e := Nat.mul_lt_mul_of_pos_left htle (Nat.pow_pos (by decide))
    rw [← Nat.pow_add] at this
    omega

/-- Für `e ≤ 3` Halbierungen gibt es (für jedes `o`) nur den trivialen 1-Zyklus `1 → 2 → 1`. -/
theorem steiner_small_e (m o e : Nat) (hm : 0 < m) (ho : 1 ≤ o) (he : e ≤ 3)
    (hodd : ∀ j, j < o → Titer j m % 2 = 1) (hk : Titer o m = 2 ^ e * m) :
    m = 1 ∧ o = 1 ∧ e = 1 := by
  obtain ⟨_, t, ht1, ht, heq⟩ := steiner_shape m o e hm ho hodd hk
  obtain ⟨_, ho2, _, _⟩ := steiner_bounds m o e hm ho hodd hk
  have : e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases this with rfl | rfl | rfl
  · have : o = 1 := by omega
    subst this; simp at heq ht; omega
  · have : o = 1 ∨ o = 2 ∨ o = 3 := by omega
    rcases this with rfl | rfl | rfl <;> simp at heq <;> omega
  · have : o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> simp at heq <;> omega

end Collatz
