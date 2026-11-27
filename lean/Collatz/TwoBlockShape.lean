import Collatz.SteinerShape

/-!
# Satz 74: Normalform der 2-Zyklen

Ein **2-Zyklus** besteht aus zwei Blöcken: Aus dem ungeraden `m` führen `o₁ ≥ 1` Aufstiege zu
`2^e₁ · m₂`, `e₁` Halbierungen zum ungeraden `m₂`; von dort führen `o₂ ≥ 1` Aufstiege zu
`2^e₂ · m` und `e₂` Halbierungen zurück zu `m`.

Für **alle** Blocklängen (ohne Rechenschranke) gilt:

* Der Zyklus schliesst sich: `Titer (o₁ + e₁ + (o₂ + e₂)) m = m`.
* Es gibt `t₁, t₂ ≥ 1` mit `m + 1 = 2^o₁ t₁`, `m₂ + 1 = 2^o₂ t₂` und dem linearen System
  `2^(e₁+o₂) t₂ + 1 = 3^o₁ t₁ + 2^e₁`,  `2^(e₂+o₁) t₁ + 1 = 3^o₂ t₂ + 2^e₂`.
* Daraus folgt `3^(o₁+o₂) < 2^(o₁+e₁+o₂+e₂)`.
* Bei insgesamt höchstens 3 Halbierungen (`e₁ + e₂ ≤ 3`) ist nur der triviale Zyklus möglich
  (`m = m₂ = 1`, zweimal durchlaufen), egal wie lang die Aufstiegsblöcke sind.

Der vollständige Ausschluss aller 2-Zyklen braucht (wie bei Simons 2005) Baker-Theorie.
-/

namespace Collatz

/-- Ein Aufstiegsblock: `o` ungerade Schritte von `m` nach `2^e · y`. -/
theorem tbs_block (m y o e : Nat) (hodd : ∀ j, j < o → Titer j m % 2 = 1)
    (hk : Titer o m = 2 ^ e * y) :
    ∃ t, 1 ≤ t ∧ m + 1 = 2 ^ o * t ∧ 2 ^ e * y + 1 = 3 ^ o * t := by
  have h := st_chain m o hodd o (Nat.le_refl _)
  rw [hk] at h
  have hcop : (2 ^ o).Coprime (3 ^ o) := Nat.Coprime.pow o o (by decide)
  obtain ⟨t, ht⟩ := hcop.dvd_of_dvd_mul_left ⟨2 ^ e * y + 1, h.symm⟩
  have hpos : 0 < 2 ^ o := Nat.pow_pos (by decide)
  have h2 : 2 ^ e * y + 1 = 3 ^ o * t := by
    rw [ht] at h
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h, ← Nat.mul_assoc, Nat.mul_comm (3 ^ o) (2 ^ o), Nat.mul_assoc]
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; simp at ht
    · exact h0
  exact ⟨t, ht1, ht, h2⟩

/-- **Satz 74 (Normalform der 2-Zyklen).** -/
theorem two_block_shape (m m₂ o₁ e₁ o₂ e₂ : Nat)
    (hodd₁ : ∀ j, j < o₁ → Titer j m % 2 = 1) (hk₁ : Titer o₁ m = 2 ^ e₁ * m₂)
    (hodd₂ : ∀ j, j < o₂ → Titer j m₂ % 2 = 1) (hk₂ : Titer o₂ m₂ = 2 ^ e₂ * m) :
    Titer (o₁ + e₁ + (o₂ + e₂)) m = m ∧
    ∃ t₁ t₂, 1 ≤ t₁ ∧ 1 ≤ t₂ ∧ m + 1 = 2 ^ o₁ * t₁ ∧ m₂ + 1 = 2 ^ o₂ * t₂ ∧
      2 ^ (e₁ + o₂) * t₂ + 1 = 3 ^ o₁ * t₁ + 2 ^ e₁ ∧
      2 ^ (e₂ + o₁) * t₁ + 1 = 3 ^ o₂ * t₂ + 2 ^ e₂ := by
  refine ⟨by rw [Titer_add, Titer_add, Titer_add, hk₁, st_halve, hk₂, st_halve], ?_⟩
  obtain ⟨t₁, h1, ht₁, e1⟩ := tbs_block m m₂ o₁ e₁ hodd₁ hk₁
  obtain ⟨t₂, h2, ht₂, e2⟩ := tbs_block m₂ m o₂ e₂ hodd₂ hk₂
  refine ⟨t₁, t₂, h1, h2, ht₁, ht₂, ?_, ?_⟩
  · have : 2 ^ e₁ * (m₂ + 1) = 2 ^ (e₁ + o₂) * t₂ := by
      rw [ht₂, Nat.pow_add, Nat.mul_assoc]
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  · have : 2 ^ e₂ * (m + 1) = 2 ^ (e₂ + o₁) * t₁ := by
      rw [ht₁, Nat.pow_add, Nat.mul_assoc]
    rw [Nat.mul_add, Nat.mul_one] at this
    omega

/-- Folgerung: `3^(o₁+o₂) < 2^(o₁+e₁+o₂+e₂)` für jeden 2-Zyklus mit `e₁, e₂ ≥ 1`. -/
theorem two_block_growth (m m₂ o₁ e₁ o₂ e₂ : Nat) (he₁ : 1 ≤ e₁) (he₂ : 1 ≤ e₂)
    (hodd₁ : ∀ j, j < o₁ → Titer j m % 2 = 1) (hk₁ : Titer o₁ m = 2 ^ e₁ * m₂)
    (hodd₂ : ∀ j, j < o₂ → Titer j m₂ % 2 = 1) (hk₂ : Titer o₂ m₂ = 2 ^ e₂ * m) :
    3 ^ (o₁ + o₂) < 2 ^ (o₁ + e₁ + (o₂ + e₂)) := by
  obtain ⟨_, t₁, t₂, h1, h2, _, _, q1, q2⟩ :=
    two_block_shape m m₂ o₁ e₁ o₂ e₂ hodd₁ hk₁ hodd₂ hk₂
  have c1 : 2 ≤ 2 ^ e₁ := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) he₁; simpa using this
  have c2 : 2 ≤ 2 ^ e₂ := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) he₂; simpa using this
  generalize hA : 2 ^ (e₁ + o₂) = A at q1
  generalize hB : 2 ^ (e₂ + o₁) = B at q2
  have i1 : 3 ^ o₁ * t₁ + 1 ≤ A * t₂ := by omega
  have i2 : 3 ^ o₂ * t₂ + 1 ≤ B * t₁ := by omega
  have hp := Nat.mul_le_mul i1 i2
  have key : 3 ^ o₁ * 3 ^ o₂ * (t₁ * t₂) < A * B * (t₁ * t₂) := by
    have e3 : (3 ^ o₁ * t₁ + 1) * (3 ^ o₂ * t₂ + 1)
        = 3 ^ o₁ * 3 ^ o₂ * (t₁ * t₂) + (3 ^ o₁ * t₁ + 3 ^ o₂ * t₂ + 1) := by grind
    have e4 : A * t₂ * (B * t₁) = A * B * (t₁ * t₂) := by grind
    omega
  have hlt := Nat.lt_of_mul_lt_mul_right key
  rw [← Nat.pow_add, ← hA, ← hB, ← Nat.pow_add] at hlt
  rw [show o₁ + e₁ + (o₂ + e₂) = e₁ + o₂ + (e₂ + o₁) by omega]
  exact hlt

/-- Bei höchstens 3 Halbierungen insgesamt gibt es (für alle Aufstiegslängen) nur den trivialen
Zyklus `1 → 2 → 1`, zweimal durchlaufen. -/
theorem two_block_small_e (m m₂ o₁ e₁ o₂ e₂ : Nat) (ho₁ : 1 ≤ o₁) (ho₂ : 1 ≤ o₂)
    (he₁ : 1 ≤ e₁) (he₂ : 1 ≤ e₂) (hE : e₁ + e₂ ≤ 3)
    (hodd₁ : ∀ j, j < o₁ → Titer j m % 2 = 1) (hk₁ : Titer o₁ m = 2 ^ e₁ * m₂)
    (hodd₂ : ∀ j, j < o₂ → Titer j m₂ % 2 = 1) (hk₂ : Titer o₂ m₂ = 2 ^ e₂ * m) :
    m = 1 ∧ m₂ = 1 ∧ o₁ = 1 ∧ o₂ = 1 ∧ e₁ = 1 ∧ e₂ = 1 := by
  have hg := two_block_growth m m₂ o₁ e₁ o₂ e₂ he₁ he₂ hodd₁ hk₁ hodd₂ hk₂
  obtain ⟨_, t₁, t₂, h1, h2, ht₁, ht₂, q1, q2⟩ :=
    two_block_shape m m₂ o₁ e₁ o₂ e₂ hodd₁ hk₁ hodd₂ hk₂
  have hO : o₁ + o₂ ≤ 5 := by
    apply Classical.byContradiction
    intro hn
    have a := st_pow_ge (o₁ + o₂) 3 (by omega)
    have b : 2 ^ (o₁ + e₁ + (o₂ + e₂)) ≤ 2 ^ (o₁ + o₂ + 3) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hE' : (e₁ = 1 ∧ e₂ = 1) ∨ (e₁ = 1 ∧ e₂ = 2) ∨ (e₁ = 2 ∧ e₂ = 1) := by omega
  have ho1 : o₁ = 1 ∨ o₁ = 2 ∨ o₁ = 3 ∨ o₁ = 4 := by omega
  have ho2 : o₂ = 1 ∨ o₂ = 2 ∨ o₂ = 3 ∨ o₂ = 4 := by omega
  rcases hE' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases ho1 with rfl | rfl | rfl | rfl <;>
  rcases ho2 with rfl | rfl | rfl | rfl <;>
  simp at q1 q2 ht₁ ht₂ hO <;> omega

end Collatz
