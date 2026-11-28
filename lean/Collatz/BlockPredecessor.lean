import Collatz.AscentExact
import Collatz.DenseTree

/-!
# Satz 85: Jede Aufstiegslänge ist rückwärts realisierbar

Ist `y` ungerade und nicht durch 3 teilbar, so gibt es zu **jedem** `o ≥ 1` eine ungerade
Zahl `m`, deren Block genau `o` Aufstiege hat und bei `y` endet:
`T^o(m) = 2^e · y` mit `e ≥ 1`.

Beweis: Da 2 Primitivwurzel modulo `3^o` ist (DenseTree), gibt es `e ≥ 1` mit
`3^o ∣ 2^e · y + 1`. Mit `2^e · y + 1 = 3^o · t` ist `t` ungerade, und `m = 2^o · t − 1`
hat nach Satz 82 genau `o` Aufstiege mit `T^o(m) + 1 = 3^o · t`.

Der Rückwärtsbaum der Blockabbildung verzweigt also an jedem Knoten `y ≢ 0 (mod 3)` in
Vorgänger mit beliebig langen Aufstiegsphasen.
-/

namespace Collatz

/-- **Satz 85.** -/
theorem block_predecessor (y o : Nat) (hy : y % 2 = 1) (h3 : y % 3 ≠ 0) (ho : 1 ≤ o) :
    ∃ m e, 1 ≤ e ∧ m % 2 = 1 ∧ (∀ j, j < o → Titer j m % 2 = 1) ∧ Titer o m = 2 ^ e * y := by
  have h3o : 3 ≤ 3 ^ o := by
    obtain ⟨p, rfl⟩ : ∃ p, o = p + 1 := ⟨o - 1, by omega⟩
    rw [Nat.pow_succ]; have := Nat.one_le_pow p 3 (by decide); omega
  have hm3 : (3 ^ o) % 3 = 0 := by
    obtain ⟨p, rfl⟩ : ∃ p, o = p + 1 := ⟨o - 1, by omega⟩
    rw [Nat.pow_succ, Nat.mul_mod_left]
  have htgt : (3 ^ o - 1) % 3 ≠ 0 := by omega
  obtain ⟨a, b, h⟩ := two_pow_hits o (2 * y) (3 ^ o - 1) (by omega) htgt (by omega)
  have hey : 2 ^ (a + 1) * y + 1 = 3 ^ o * (b + 1) := by
    have : 2 ^ (a + 1) * y = 2 ^ a * (2 * y) := by rw [Nat.pow_succ]; grind
    rw [this, h, Nat.mul_add, Nat.mul_one]; omega
  have hodd3 : (3 ^ o) % 2 = 1 := by rw [Nat.pow_mod]; simp
  have hev : (2 ^ (a + 1) * y) % 2 = 0 := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc, Nat.mul_mod_right]
  have htodd : (b + 1) % 2 = 1 := by
    have : (3 ^ o * (b + 1)) % 2 = 1 := by rw [← hey]; omega
    rw [Nat.mul_mod, hodd3] at this; omega
  have hp : 1 ≤ 2 ^ o * (b + 1) := Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
  have hm : 2 ^ o * (b + 1) - 1 + 1 = 2 ^ o * (b + 1) := by omega
  obtain ⟨hasc, hval⟩ := ascent_exact o (2 ^ o * (b + 1) - 1) (b + 1) hm
  refine ⟨2 ^ o * (b + 1) - 1, a + 1, by omega, ?_, hasc, ?_⟩
  · have := hasc 0 (by omega); simpa [Titer] using this
  · omega

end Collatz
