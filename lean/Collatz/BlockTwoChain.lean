import Collatz.BlockResidues

/-!
# Satz 81: Die 2-adische Kette der Blöcke

Zwei aufeinander folgende Blöcke `m → y → z` (Satz 74) mit `m + 1 = 2^o · t` und
`y + 1 = 2^o' · t'`. Dann ist

  `3^o · t + 2^e − 1 = 2^(e + o') · t'`  mit ungeradem `t'`,

d. h. die 2-Potenz in `3^o · t + 2^e − 1` ist **genau** `2^(e + o')`. Das ist das
Gegenstück zu Satz 80: dort steuert der Rest modulo 3 die 3-Potenz, hier legen die
Halbierungszahl `e` des einen und die Aufstiegszahl `o'` des nächsten Blocks die
2-Potenz exakt fest.
-/

namespace Collatz

/-- **Satz 81.** -/
theorem block_two_chain (m y z o e o' e' : Nat) (ho' : 0 < o') (he' : 0 < e')
    (hodd : ∀ j, j < o → Titer j m % 2 = 1) (hk : Titer o m = 2 ^ e * y)
    (hodd' : ∀ j, j < o' → Titer j y % 2 = 1) (hk' : Titer o' y = 2 ^ e' * z) :
    3 ^ o * ((m + 1) / 2 ^ o) + 2 ^ e - 1 = 2 ^ (e + o') * ((y + 1) / 2 ^ o') ∧
    ((y + 1) / 2 ^ o') % 2 = 1 ∧
    ¬ 2 ^ (e + o' + 1) ∣ 3 ^ o * ((m + 1) / 2 ^ o) + 2 ^ e - 1 := by
  obtain ⟨t, _, ht, h2⟩ := tbs_block m y o e hodd hk
  obtain ⟨t', _, ht', _⟩ := tbs_block y z o' e' hodd' hk'
  obtain ⟨htodd, _, _⟩ := block_residues y z o' e' ho' he' hodd' hk'
  have hp : 0 < 2 ^ o := Nat.pow_pos (by decide)
  have hp' : 0 < 2 ^ o' := Nat.pow_pos (by decide)
  have hd : (m + 1) / 2 ^ o = t := by rw [ht, Nat.mul_div_cancel_left _ hp]
  have hd' : (y + 1) / 2 ^ o' = t' := by rw [ht', Nat.mul_div_cancel_left _ hp']
  rw [hd'] at htodd
  rw [hd, hd']
  have he1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have heq : 3 ^ o * t + 2 ^ e - 1 = 2 ^ (e + o') * t' := by
    have : 3 ^ o * t + 2 ^ e - 1 = 2 ^ e * (y + 1) := by
      rw [← h2, Nat.mul_add, Nat.mul_one]; omega
    rw [this, ht', Nat.pow_add, Nat.mul_assoc]
  refine ⟨heq, htodd, ?_⟩
  rw [heq, Nat.pow_succ]
  intro hdv
  have hq : 0 < 2 ^ (e + o') := Nat.pow_pos (by decide)
  have : 2 ∣ t' := (Nat.mul_dvd_mul_iff_left hq).mp hdv
  omega

end Collatz
