import Collatz.DoubleOddCount
import Collatz.Density
import Collatz.OrbitDensity

/-!
# Satz 64: In einem Gegenbeispiel beginnt mindestens jeder vierte Schritt einen Doppel-Aufstieg

Rein kombinatorisch gilt für jede Paritätsfolge: Jeder Lauf ungerader Schritte der Länge `L`
enthält `L-1` Doppel-Aufstiege und endet mit einem geraden Schritt. Daraus folgt

  `2 · (#ungerade unter den ersten J) ≤ J + (#Doppel-Aufstiege) + 1`.

Zusammen mit der Dichteschranke (Satz 32: ein Gegenbeispiel hat zu jeder Zeit mehr als 5/8
ungerade Schritte) erhält man: Ab dem kleinsten Glied eines Gegenbeispiels beginnt unter den
ersten `J` Schritten an mindestens `J/4 - 1` Stellen ein Doppel-Aufstieg. Aus dem
logarithmischen Wachstum von Satz 63 wird so ein linearer Anteil.
-/

namespace Collatz

theorem dd_par (j n : Nat) : nthPar (0 + j) n = (Titer j n % 2 == 1) := by
  unfold nthPar; rw [Nat.zero_add]

theorem dd_step (j n : Nat) :
    2 * oddsT (j + 1) n ≤ j + doCnt n 0 j + (if Titer j n % 2 = 1 then 1 else 0) + 1 := by
  induction j with
  | zero => simp [oddsT, doCnt, Titer]; split <;> omega
  | succ j ih =>
    rw [oddsT_succ (j + 1) n]
    simp only [doCnt]
    rw [dd_par, show 0 + j + 1 = 0 + (j + 1) by omega, dd_par]
    rcases Nat.mod_two_eq_zero_or_one (Titer j n) with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one (Titer (j + 1) n) with h2 | h2 <;>
    simp [h1, h2] at ih ⊢ <;> omega

/-- **Kombinatorik der Läufe:** `2·o ≤ J + c + 1`. -/
theorem odds_le_double_odd (J n : Nat) : 2 * oddsT J n ≤ J + doCnt n 0 J + 1 := by
  cases J with
  | zero => simp [oddsT]
  | succ j =>
    have h := dd_step j n
    have hm := doCnt_mono n 0 (show j ≤ j + 1 by omega)
    split at h <;> omega

/-- Aus `2^j · b^o ≤ a^o` mit `a^5 ≤ 2^8 · b^5` und `b < a` folgt `5j ≤ 8o`. -/
theorem dd_ratio {a b o j : Nat} (hab : b < a) (h : 2 ^ j * b ^ o ≤ a ^ o)
    (h85 : a ^ 5 ≤ 2 ^ 8 * b ^ 5) : 5 * j ≤ 8 * o := by
  apply Nat.le_of_not_lt
  intro hlt
  obtain ⟨d, hd⟩ : ∃ d, 5 * j = 8 * o + (d + 1) := ⟨5 * j - 8 * o - 1, by omega⟩
  have h8 : (2 ^ j * b ^ o) ^ 8 ≤ (a ^ o) ^ 8 := Nat.pow_le_pow_left h 8
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at h8
  have h5 : (a ^ 5) ^ j ≤ (2 ^ 8 * b ^ 5) ^ j := Nat.pow_le_pow_left h85 j
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at h5
  rw [show 5 * j = 8 * o + (d + 1) by omega] at h5
  rw [show 8 * j = j * 8 by omega] at h5
  rw [Nat.pow_add a (8 * o) (d + 1), Nat.pow_add b (8 * o) (d + 1)] at h5
  have hlt' : b ^ (d + 1) < a ^ (d + 1) := Nat.pow_lt_pow_left hab (by omega)
  have hpos : 0 < a ^ (8 * o) := Nat.pow_pos (by omega)
  rw [show o * 8 = 8 * o by omega] at h8
  -- a^(8o)·a^(d+1) ≤ 2^(8j)·b^(8o)·b^(d+1) ≤ a^(8o)·b^(d+1)
  have h9 : 2 ^ (j * 8) * (b ^ (8 * o) * b ^ (d + 1)) ≤ a ^ (8 * o) * b ^ (d + 1) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ h8
  have h10 : a ^ (8 * o) * a ^ (d + 1) ≤ a ^ (8 * o) * b ^ (d + 1) := Nat.le_trans h5 h9
  have := Nat.le_of_mul_le_mul_left h10 hpos
  omega

theorem dd_const : (3 * 134217728 + 1) ^ 5 ≤ 2 ^ 8 * 134217728 ^ 5 := by decide

/-- **Satz 64.** Ist `m ≥ 2^27` ein Bahnminimum (wie das kleinste Glied eines
Gegenbeispiels, Satz 27), so beginnt unter den ersten `J` Schritten an mindestens
`J/4 - 1` Stellen ein Doppel-Aufstieg: `J ≤ 4·(doCnt + 1)`. -/
theorem orbitMin_double_odd_density {m : Nat} (hbig : 134217728 ≤ m) (hmin : IsOrbitMin m)
    (J : Nat) : J ≤ 4 * (doCnt m 0 J + 1) := by
  have hd := density_mono (by decide) hbig (orbitMin_density (by omega) hmin J)
  have h58 := dd_ratio (by decide) hd dd_const
  have h2 := odds_le_double_odd J m
  omega

end Collatz
