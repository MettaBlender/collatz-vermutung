import Collatz.Verified

/-!
# Nachgerechnet bis 100 000

Wie in `Verified.lean`, aber schneller: Gerade Zahlen und `n ≡ 1 (mod 4)` fallen
bewiesenermassen ab (`descends_of_even`, `descends_of_mod_four_eq_one`). Der Kernel
muss also nur noch `n ≡ 3 (mod 4)` prüfen. Damit der Speicher reicht, wird in Blöcken
zu je 10 000 Zahlen gerechnet.
-/

namespace Collatz

/-- Prüft alle `m` mit `lo ≤ m < lo + len` und `m ≡ 3 (mod 4)`. -/
def descendRange (fuel lo : Nat) : (len : Nat) → Bool
  | 0 => true
  | len + 1 =>
    ((lo + len) % 4 != 3 || descendsWithin (lo + len) fuel (lo + len)) && descendRange fuel lo len

theorem descends_of_descendRange {fuel lo : Nat} :
    ∀ len, descendRange fuel lo len = true → ∀ m, lo ≤ m → m < lo + len → 1 < m → Descends m := by
  intro len
  induction len with
  | zero => intro _ m h1 h2; omega
  | succ len ih =>
    intro h m hlo hhi h1
    unfold descendRange at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨hm, hrest⟩ := h
    by_cases hml : m = lo + len
    · subst hml
      by_cases h3 : (lo + len) % 4 = 3
      · rcases hm with h' | h'
        · exact absurd h3 h'
        · exact descendsWithin_sound _ fuel _ h'
      · have : (lo + len) % 4 = 0 ∨ (lo + len) % 4 = 1 ∨ (lo + len) % 4 = 2 := by omega
        rcases this with h0 | h0 | h0
        · exact descends_of_even (by omega) (by omega)
        · exact descends_of_mod_four_eq_one h1 h0
        · exact descends_of_even (by omega) (by omega)
    · exact ih hrest m hlo (by omega) h1

theorem block0 : descendRange 400 2 9998 = true := by decide +kernel
theorem block1 : descendRange 400 10000 10000 = true := by decide +kernel
theorem block2 : descendRange 400 20000 10000 = true := by decide +kernel
theorem block3 : descendRange 400 30000 10000 = true := by decide +kernel
theorem block4 : descendRange 400 40000 10000 = true := by decide +kernel
theorem block5 : descendRange 400 50000 10000 = true := by decide +kernel
theorem block6 : descendRange 400 60000 10000 = true := by decide +kernel
theorem block7 : descendRange 400 70000 10000 = true := by decide +kernel
theorem block8 : descendRange 400 80000 10000 = true := by decide +kernel
theorem block9 : descendRange 400 90000 10001 = true := by decide +kernel

theorem descends_upto_100000 : ∀ m, 1 < m → m ≤ 100000 → Descends m := by
  intro m h1 hm
  have : m < 10000 ∨ (10000 ≤ m ∧ m < 20000) ∨ (20000 ≤ m ∧ m < 30000) ∨
      (30000 ≤ m ∧ m < 40000) ∨ (40000 ≤ m ∧ m < 50000) ∨ (50000 ≤ m ∧ m < 60000) ∨
      (60000 ≤ m ∧ m < 70000) ∨ (70000 ≤ m ∧ m < 80000) ∨ (80000 ≤ m ∧ m < 90000) ∨
      90000 ≤ m := by omega
  rcases this with h | h | h | h | h | h | h | h | h | h
  · exact descends_of_descendRange _ block0 m (by omega) (by omega) h1
  · exact descends_of_descendRange _ block1 m (by omega) (by omega) h1
  · exact descends_of_descendRange _ block2 m (by omega) (by omega) h1
  · exact descends_of_descendRange _ block3 m (by omega) (by omega) h1
  · exact descends_of_descendRange _ block4 m (by omega) (by omega) h1
  · exact descends_of_descendRange _ block5 m (by omega) (by omega) h1
  · exact descends_of_descendRange _ block6 m (by omega) (by omega) h1
  · exact descends_of_descendRange _ block7 m (by omega) (by omega) h1
  · exact descends_of_descendRange _ block8 m (by omega) (by omega) h1
  · exact descends_of_descendRange _ block9 m (by omega) (by omega) h1

/-- **Alle Zahlen von 1 bis 100 000 erreichen die 1** (vom Lean-Kernel nachgerechnet). -/
theorem reachesOne_upto_100000 : ∀ n, 0 < n → n ≤ 100000 → ReachesOne n :=
  reachesOne_of_descends_upto 100000 descends_upto_100000

end Collatz
