import Collatz.BlockResidues

/-!
# Satz 82: Die Aufstiegslänge ist genau die Binärendung

Umkehrung von Satz 74/79: Ist `m + 1 = 2^o · t`, so sind die ersten `o` Schritte von `m`
Aufstiege, und nach ihnen gilt `T^o(m) + 1 = 3^o · t`. Ist zusätzlich `t` ungerade, so ist
`T^o(m)` gerade, der Aufstieg endet also **genau** nach `o` Schritten.

Zusammen mit Satz 79: Eine ungerade Zahl `m` hat genau `o` Aufstiege
**genau dann, wenn** `m ≡ 2^o − 1 (mod 2^(o+1))`. Die Aufstiegslänge ist also eine reine
Funktion der letzten Binärziffern, für alle natürlichen Zahlen.
-/

namespace Collatz

theorem ae_step (x a c : Nat) (h : x + 1 = 2 ^ (a + 1) * c) :
    x % 2 = 1 ∧ T x + 1 = 2 ^ a * (3 * c) := by
  have hx : x = 2 * (2 ^ a * c) - 1 := by rw [Nat.pow_succ] at h; grind
  have hpos : 0 < 2 ^ a * c := by
    rcases Nat.eq_zero_or_pos (2 ^ a * c) with h0 | h0
    · rw [Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc, h0] at h; omega
    · exact h0
  have hodd : x % 2 = 1 := by omega
  refine ⟨hodd, ?_⟩
  unfold T
  rw [if_neg (by omega)]
  have : 3 * x + 1 = 2 * (3 * (2 ^ a * c)) - 2 := by omega
  rw [this]
  have : 2 * (3 * (2 ^ a * c)) - 2 = 2 * (3 * (2 ^ a * c) - 1) := by omega
  rw [this, Nat.mul_div_cancel_left _ (by decide)]
  have : 1 ≤ 3 * (2 ^ a * c) := by omega
  rw [Nat.sub_add_cancel this]
  grind

/-- **Satz 82 (Teil 1).** `m + 1 = 2^o · t` erzwingt `o` Aufstiege. -/
theorem ascent_exact (o : Nat) : ∀ m t, m + 1 = 2 ^ o * t →
    (∀ j, j < o → Titer j m % 2 = 1) ∧ Titer o m + 1 = 3 ^ o * t := by
  induction o with
  | zero => intro m t h; refine ⟨fun j hj => absurd hj (by omega), ?_⟩; simpa [Titer] using h
  | succ o ih =>
    intro m t h
    obtain ⟨hodd, hT⟩ := ae_step m o t h
    obtain ⟨ih1, ih2⟩ := ih (T m) (3 * t) hT
    refine ⟨?_, ?_⟩
    · intro j hj
      cases j with
      | zero => simpa [Titer] using hodd
      | succ j => show Titer j (T m) % 2 = 1; exact ih1 j (by omega)
    · show Titer o (T m) + 1 = 3 ^ (o + 1) * t
      rw [ih2, Nat.pow_succ]; grind

/-- **Satz 82 (Teil 2).** Mit ungeradem `t` endet der Aufstieg genau nach `o` Schritten. -/
theorem ascent_stops (o m t : Nat) (h : m + 1 = 2 ^ o * t) (ht : t % 2 = 1) :
    (∀ j, j < o → Titer j m % 2 = 1) ∧ Titer o m % 2 = 0 := by
  obtain ⟨h1, h2⟩ := ascent_exact o m t h
  refine ⟨h1, ?_⟩
  have h3 : (3 ^ o * t) % 2 = 1 := by
    rw [Nat.mul_mod, Nat.pow_mod]; simp [ht]
  omega

/-- **Satz 82 (Charakterisierung).** Für `o ≥ 1`, `e ≥ 1`: ein Block der Form
`T^o(m) = 2^e · y` existiert genau dann, wenn `m ≡ 2^o − 1 (mod 2^(o+1))` gilt
(die Richtung „⇒“ ist Satz 79, hier die Richtung „⇐“). -/
theorem ascent_iff_residue (o m : Nat) (ho : 0 < o) (hm : m % 2 ^ (o + 1) = 2 ^ o - 1) :
    (∀ j, j < o → Titer j m % 2 = 1) ∧ Titer o m % 2 = 0 := by
  have hp : 0 < 2 ^ o := Nat.pow_pos (by decide)
  have hdm := Nat.div_add_mod m (2 ^ (o + 1))
  rw [hm, Nat.pow_succ] at hdm
  refine ascent_stops o m (2 * (m / (2 ^ o * 2)) + 1) ?_ (by omega)
  have : 2 ^ o * (2 * (m / (2 ^ o * 2)) + 1) = 2 ^ o * 2 * (m / (2 ^ o * 2)) + 2 ^ o := by grind
  omega

end Collatz
