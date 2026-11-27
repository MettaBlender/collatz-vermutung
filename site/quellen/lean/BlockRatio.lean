import Collatz.TwoBlockShape

/-!
# Satz 76: Die exakte Blockabbildung und das Verhalten am Minimum

Ein Block (Satz 74) führt eine ungerade Zahl `m` mit `o` Aufstiegen zu `2^e · y` und danach mit
`e` Halbierungen zur ungeraden Zahl `y`. Dann gilt die **exakte Blockabbildung**

  `2^(o+e) · y + 2^o = 3^o · (m + 1)`,

also `y = (3^o (m+1) − 2^o) / 2^(o+e)`. Folgerungen für `o ≥ 1`:

* `3^o · m < 2^(o+e) · y` (jeder Block wächst höchstens um den Faktor `3^o / 2^(o+e)` plus Rest);
* fällt der Block nicht (`m ≤ y`, etwa wenn `m` das Minimum eines Zyklus ist), so gilt
  `2^(o+e) · m < 3^o · (m + 1)`; ist zudem `3^o ≤ m`, sogar `2^(o+e) < 3^o`:
  der Block am Minimum eines grossen Zyklus hat weniger als `o · log₂ 3 − o` Halbierungen;
* steigt der Block nicht (`y ≤ m`, etwa wenn `m` das Maximum der Blockstarts ist), so gilt
  `3^o < 2^(o+e)`.
-/

namespace Collatz

/-- **Satz 76a.** Exakte Blockabbildung. -/
theorem block_map (m y o e : Nat) (hodd : ∀ j, j < o → Titer j m % 2 = 1)
    (hk : Titer o m = 2 ^ e * y) :
    2 ^ (o + e) * y + 2 ^ o = 3 ^ o * (m + 1) := by
  obtain ⟨t, _, ht, h2⟩ := tbs_block m y o e hodd hk
  have h3 := congrArg (fun x => 2 ^ o * x) h2
  simp only [Nat.mul_add, Nat.mul_one] at h3
  rw [ht, Nat.pow_add]
  grind

/-- **Satz 76b.** Wachstum, Minimum- und Maximum-Verhalten eines Blocks. -/
theorem block_ratio (m y o e : Nat) (ho : 0 < o) (hodd : ∀ j, j < o → Titer j m % 2 = 1)
    (hk : Titer o m = 2 ^ e * y) :
    3 ^ o * m < 2 ^ (o + e) * y ∧
    (m ≤ y → 2 ^ (o + e) * m < 3 ^ o * (m + 1)) ∧
    (m ≤ y → 3 ^ o ≤ m → 2 ^ (o + e) < 3 ^ o) ∧
    (y ≤ m → 0 < m → 3 ^ o < 2 ^ (o + e)) := by
  have hmap := block_map m y o e hodd hk
  have h23 : 2 ^ o < 3 ^ o := Nat.pow_lt_pow_left (by decide) (by omega)
  have hpos : 0 < 2 ^ o := Nat.pow_pos (by decide)
  generalize hA : 2 ^ (o + e) = A at hmap ⊢
  generalize hB : 2 ^ o = B at hmap h23 hpos
  generalize hC : 3 ^ o = C at hmap h23 ⊢
  rw [Nat.mul_add, Nat.mul_one] at hmap
  have g1 : C * m < A * y := by omega
  refine ⟨g1, ?_, ?_, ?_⟩
  · intro hmy
    have : A * m ≤ A * y := Nat.mul_le_mul_left _ hmy
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · intro hmy hCm
    have h1 : A * m ≤ A * y := Nat.mul_le_mul_left _ hmy
    have h2 : A * m < C * m + C := by omega
    have h3 : A * m < C * m + m := by omega
    have h4 : A * m < (C + 1) * m := by rw [Nat.add_mul, Nat.one_mul]; exact h3
    have h5 : A < C + 1 := Nat.lt_of_mul_lt_mul_right h4
    rcases Nat.lt_or_ge A C with h | h
    · exact h
    · -- A = C unmöglich: 2-Potenz gegen 3-Potenz
      exfalso
      have hAC : A = C := by omega
      have hev : A % 2 = 0 := by
        obtain ⟨p, hp⟩ : ∃ p, o + e = p + 1 := ⟨o + e - 1, by omega⟩
        rw [← hA, hp, Nat.pow_succ, Nat.mul_mod_left]
      have hodd3 : C % 2 = 1 := by rw [← hC, Nat.pow_mod]; simp
      omega
  · intro hym hm
    have h1 : A * y ≤ A * m := Nat.mul_le_mul_left _ hym
    have h2 : C * m < A * m := by omega
    exact Nat.lt_of_mul_lt_mul_right h2

end Collatz
