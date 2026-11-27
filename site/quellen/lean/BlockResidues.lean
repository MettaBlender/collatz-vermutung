import Collatz.TwoBlockShape

/-!
# Satz 79: Die Restklassen-Signatur eines Blocks

Ein Block (Satz 74) führt die ungerade Zahl `m` mit `o ≥ 1` Aufstiegen zu `2^e · y` und mit
`e ≥ 1` Halbierungen zur ungeraden Zahl `y`. Mit `m + 1 = 2^o · t` gilt dann:

* `t` ist ungerade, also ist `m ≡ 2^o − 1 (mod 2^(o+1))`: die Länge des Aufstiegs ist an den
  letzten `o + 1` Binärziffern von `m` exakt ablesbar;
* `y` ist nie durch 3 teilbar, genauer `y ≡ 1 (mod 3)` für ungerades `e` und `y ≡ 2 (mod 3)`
  für gerades `e`: die Parität der Halbierungszahl ist am nächsten Blockstart modulo 3 ablesbar.

In einem Zyklus ist also jeder Blockstart `≢ 0 (mod 3)`, und die Folge der Paritäten der `eᵢ`
ist durch die Reste der Blockstarts modulo 3 festgelegt.
-/

namespace Collatz

theorem two_pow_mod_three (e : Nat) : 2 ^ e % 3 = if e % 2 = 0 then 1 else 2 := by
  induction e with
  | zero => decide
  | succ e ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]
    split <;> split <;> omega

/-- **Satz 79.** Restklassen-Signatur eines Blocks. -/
theorem block_residues (m y o e : Nat) (ho : 0 < o) (he : 0 < e)
    (hodd : ∀ j, j < o → Titer j m % 2 = 1) (hk : Titer o m = 2 ^ e * y) :
    ((m + 1) / 2 ^ o) % 2 = 1 ∧
    m % 2 ^ (o + 1) = 2 ^ o - 1 ∧
    y % 3 = (if e % 2 = 0 then 2 else 1) := by
  obtain ⟨t, ht1, ht, h2⟩ := tbs_block m y o e hodd hk
  have hpos : 0 < 2 ^ o := Nat.pow_pos (by decide)
  have hdiv : (m + 1) / 2 ^ o = t := by rw [ht, Nat.mul_div_cancel_left _ hpos]
  -- t ungerade
  have h2e : (2 ^ e * y) % 2 = 0 := by
    obtain ⟨p, rfl⟩ : ∃ p, e = p + 1 := ⟨e - 1, by omega⟩
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ p) 2, Nat.mul_assoc, Nat.mul_mod_right]
  have h3o : (3 ^ o) % 2 = 1 := by rw [Nat.pow_mod]; simp
  have htodd : t % 2 = 1 := by
    have : (3 ^ o * t) % 2 = (2 ^ e * y + 1) % 2 := by rw [h2]
    rw [Nat.mul_mod, h3o] at this
    omega
  refine ⟨by rw [hdiv]; exact htodd, ?_, ?_⟩
  · -- m = 2^(o+1) s + 2^o - 1
    obtain ⟨s, hs⟩ : ∃ s, t = 2 * s + 1 := ⟨t / 2, by omega⟩
    have hm : m + 1 = 2 ^ (o + 1) * s + 2 ^ o := by
      rw [ht, hs, Nat.pow_succ]; grind
    have hlt : 2 ^ o - 1 < 2 ^ (o + 1) := by rw [Nat.pow_succ]; omega
    have : m = 2 ^ (o + 1) * s + (2 ^ o - 1) := by omega
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  · -- 2^e y ≡ -1 (mod 3)
    have h33 : (3 ^ o * t) % 3 = 0 := by
      obtain ⟨p, rfl⟩ : ∃ p, o = p + 1 := ⟨o - 1, by omega⟩
      rw [Nat.pow_succ, Nat.mul_comm (3 ^ p) 3, Nat.mul_assoc, Nat.mul_mod_right]
    have hsum : (2 ^ e * y + 1) % 3 = 0 := by rw [h2]; exact h33
    have hm3 : (2 ^ e * y) % 3 = ((2 ^ e % 3) * (y % 3)) % 3 := Nat.mul_mod _ _ _
    rw [two_pow_mod_three] at hm3
    have hy : y % 3 < 3 := Nat.mod_lt _ (by decide)
    split
    · rename_i hev
      rw [if_pos hev] at hm3
      omega
    · rename_i hev
      rw [if_neg hev] at hm3
      have : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
      rcases this with h | h | h <;> rw [h] at hm3 <;> omega

end Collatz
