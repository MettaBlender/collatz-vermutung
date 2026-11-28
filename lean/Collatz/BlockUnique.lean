import Collatz.BlockDecomp
import Collatz.Crandall

/-!
# Satz 84: Die Blockzerlegung ist eindeutig

Die Zerlegung aus Satz 83 ist eindeutig: Gilt für eine ungerade Zahl `m`

* die ersten `o` Schritte sind Aufstiege und `T^o(m) = 2^e · y` mit `e ≥ 1`, `y` ungerade,
* ebenso mit `(o', e', y')`,

so ist `o = o'`, `e = e'` und `y = y'`. Damit ist die **Blockabbildung**
`B(m) = y` eine wohldefinierte Funktion auf den ungeraden Zahlen, und jede Bahn hat genau
eine Blockfolge `(o₁, e₁), (o₂, e₂), …`.
-/

namespace Collatz

/-- **Satz 84.** -/
theorem block_unique (m o e y o' e' y' : Nat) (he : 1 ≤ e) (he' : 1 ≤ e')
    (hy : y % 2 = 1) (hy' : y' % 2 = 1)
    (hodd : ∀ j, j < o → Titer j m % 2 = 1) (hk : Titer o m = 2 ^ e * y)
    (hodd' : ∀ j, j < o' → Titer j m % 2 = 1) (hk' : Titer o' m = 2 ^ e' * y') :
    o = o' ∧ e = e' ∧ y = y' := by
  have hev : ∀ a b, 1 ≤ a → (2 ^ a * b) % 2 = 0 := by
    intro a b ha
    obtain ⟨p, rfl⟩ : ∃ p, a = p + 1 := ⟨a - 1, by omega⟩
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ p) 2, Nat.mul_assoc, Nat.mul_mod_right]
  have hoo : o = o' := by
    rcases Nat.lt_trichotomy o o' with h | h | h
    · have := hodd' o h; rw [hk, hev e y he] at this; omega
    · exact h
    · have := hodd o' h; rw [hk', hev e' y' he'] at this; omega
  subst hoo
  have h2 : 2 ^ e * y = 2 ^ e' * y' := by rw [← hk, ← hk']
  have hyy : y = y' := odd_part_unique e e' y y' hy hy' h2
  subst hyy
  have hpos : 0 < y := by omega
  have : 2 ^ e = 2 ^ e' := Nat.eq_of_mul_eq_mul_right hpos h2
  refine ⟨rfl, ?_, rfl⟩
  rcases Nat.lt_trichotomy e e' with h | h | h
  · have := Nat.pow_lt_pow_right (show 1 < 2 by decide) h; omega
  · exact h
  · have := Nat.pow_lt_pow_right (show 1 < 2 by decide) h; omega

end Collatz
