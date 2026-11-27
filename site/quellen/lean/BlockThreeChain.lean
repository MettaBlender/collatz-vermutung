import Collatz.BlockResidues

/-!
# Satz 80: Die 3-adische Kette der Blöcke

Ein Block führt die ungerade Zahl `m` mit `o ≥ 1` Aufstiegen zu `2^e · y`
(Satz 74: `m + 1 = 2^o · t` und `2^e · y + 1 = 3^o · t`). Dann gilt

  `m ≡ 2 (mod 3)  ⟺  3^(o+1) ∣ 2^e · y + 1`,

d. h. der Rest von `m` modulo 3 entscheidet, ob die 3-Potenz in `2^e·y + 1` genau `3^o`
ist oder grösser. Zusammen mit Satz 79 (der Rest des Blockstarts modulo 3 ist durch die
Parität der vorigen Halbierungszahl festgelegt) entsteht eine Kette über zwei aufeinander
folgende Blöcke:

  `eᵢ gerade  ⟺  3^(oᵢ₊₁ + 1) ∣ 2^(eᵢ₊₁) · mᵢ₊₂ + 1`.
-/

namespace Collatz

/-- **Satz 80 (Blockebene).** -/
theorem block_three_valuation (m y o e : Nat)
    (hodd : ∀ j, j < o → Titer j m % 2 = 1) (hk : Titer o m = 2 ^ e * y) :
    3 ^ o ∣ 2 ^ e * y + 1 ∧ (m % 3 = 2 ↔ 3 ^ (o + 1) ∣ 2 ^ e * y + 1) := by
  obtain ⟨t, _, ht, h2⟩ := tbs_block m y o e hodd hk
  refine ⟨⟨t, h2⟩, ?_⟩
  have hp : 0 < 3 ^ o := Nat.pow_pos (by decide)
  have hdv : (3 ^ (o + 1) ∣ 2 ^ e * y + 1) ↔ 3 ∣ t := by
    rw [h2, Nat.pow_succ]
    exact Nat.mul_dvd_mul_iff_left hp
  rw [hdv]
  have h2o := br_two_pow_mod_three o
  have hm3 : (m + 1) % 3 = ((2 ^ o % 3) * (t % 3)) % 3 := by rw [ht, Nat.mul_mod]
  have ht3 : t % 3 < 3 := Nat.mod_lt _ (by decide)
  constructor
  · intro hm
    apply Nat.dvd_of_mod_eq_zero
    have hm1 : (m + 1) % 3 = 0 := by omega
    rw [hm1] at hm3
    split at h2o <;> rw [h2o] at hm3 <;>
      (have : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
       rcases this with h | h | h <;> rw [h] at hm3 <;> omega)
  · intro hd
    have h0 : t % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
    rw [h0, Nat.mul_zero] at hm3
    omega

/-- **Satz 80 (Kette).** Zwei aufeinander folgende Blöcke `m → y → z`. -/
theorem block_three_chain (m y z o e o' e' : Nat) (ho : 0 < o) (he : 0 < e)
    (hodd : ∀ j, j < o → Titer j m % 2 = 1) (hk : Titer o m = 2 ^ e * y)
    (hodd' : ∀ j, j < o' → Titer j y % 2 = 1) (hk' : Titer o' y = 2 ^ e' * z) :
    y % 3 ≠ 0 ∧ (e % 2 = 0 ↔ 3 ^ (o' + 1) ∣ 2 ^ e' * z + 1) := by
  obtain ⟨_, _, hy⟩ := block_residues m y o e ho he hodd hk
  obtain ⟨_, hv⟩ := block_three_valuation y z o' e' hodd' hk'
  rw [← hv, hy]
  constructor
  · split <;> omega
  · split <;> simp_all

end Collatz
