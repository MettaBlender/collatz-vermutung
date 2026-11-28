import Collatz.AscentExact

/-!
# Satz 83: Jede ungerade Zahl beginnt einen Block

Für jede ungerade Zahl `m` gibt es eindeutig bestimmte `o ≥ 1`, `e ≥ 1` und eine
ungerade Zahl `y` mit

* die ersten `o` Schritte von `m` sind Aufstiege,
* `T^o(m) = 2^e · y`, also `T^(o+e)(m) = y`.

Dabei ist `o` die Zahl der Einsen am Ende der Binärdarstellung von `m` (Satz 82) und
`T^o(m) + 1 = 3^o · t` mit `t = (m+1)/2^o`. Damit zerfällt die Bahn **jeder** ungeraden
Zahl lückenlos in Blöcke: Das Blocksystem der Sätze 74–82 beschreibt nicht nur
hypothetische Zyklen, sondern jede Collatz-Bahn.
-/

namespace Collatz

/-- Jede positive Zahl ist `2^a · u` mit ungeradem `u`. -/
theorem bd_two_pow_odd (n : Nat) (hn : 0 < n) : ∃ a u, n = 2 ^ a * u ∧ u % 2 = 1 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · obtain ⟨a, u, hu, hodd⟩ := ih (n / 2) (by omega) (by omega)
      refine ⟨a + 1, u, ?_, hodd⟩
      rw [Nat.pow_succ]; grind
    · exact ⟨0, n, by simp, h⟩

/-- **Satz 83.** Blockzerlegung jeder ungeraden Zahl. -/
theorem block_decomp (m : Nat) (hm : m % 2 = 1) :
    ∃ o e y, 1 ≤ o ∧ 1 ≤ e ∧ y % 2 = 1 ∧
      (∀ j, j < o → Titer j m % 2 = 1) ∧ Titer o m = 2 ^ e * y ∧ Titer (o + e) m = y := by
  obtain ⟨o, t, ht, htodd⟩ := bd_two_pow_odd (m + 1) (by omega)
  have ho : 1 ≤ o := by
    rcases Nat.eq_zero_or_pos o with h0 | h0
    · rw [h0, Nat.pow_zero, Nat.one_mul] at ht; omega
    · exact h0
  obtain ⟨hasc, hval⟩ := ascent_exact o m t ht
  obtain ⟨_, heven⟩ := ascent_stops o m t ht htodd
  have hpos : 0 < Titer o m := by
    have h3o : 3 ≤ 3 ^ o := by
      obtain ⟨p, rfl⟩ : ∃ p, o = p + 1 := ⟨o - 1, by omega⟩
      rw [Nat.pow_succ]; have := Nat.one_le_pow p 3 (by decide); omega
    have : 3 ≤ 3 ^ o * t := Nat.le_trans h3o (Nat.le_mul_of_pos_right _ (by omega))
    omega
  obtain ⟨e, y, hy, hyodd⟩ := bd_two_pow_odd (Titer o m) hpos
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, Nat.pow_zero, Nat.one_mul] at hy; omega
    · exact h0
  refine ⟨o, e, y, ho, he, hyodd, hasc, hy, ?_⟩
  rw [Titer_add, hy, st_halve]

end Collatz
