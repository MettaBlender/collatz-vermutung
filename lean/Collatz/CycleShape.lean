import Collatz.Verified24All

/-!
# Die Länge eines weiteren Zyklus hat eine feste Form (nach Eliahou 1993)

Für einen Zyklus mit `o` ungeraden und `e` geraden Gliedern, alle `≥ m`, gilt
`3^o < 2^e` und `2^e · m^o ≤ (3m+1)^o`. Der Bruch `e/o` liegt also zwischen `log₂ 3` und
`log₂ (3 + 1/m)`. Liegt dieses Intervall zwischen zwei Brüchen `p₁/q₁ < p₂/q₂` mit
`p₂ q₁ − p₁ q₂ = 1` (Nachbarn im Stern-Brocot-Baum), so ist `(o, e)` eine Summe
`a·(q₁, p₁) + b·(q₂, p₂)` mit ganzen `a, b ≥ 1`.

Für `m = 2^24` sind die Nachbarn `1054/665` und `18403/11611`: Jeder weitere Zyklus hat
`o = 665a + 11611b` ungerade und `e = 1054a + 18403b` gerade Glieder, also die Länge
`1719a + 30014b` mit `a, b ≥ 1`. Die kleinste mögliche Länge ist 31 733.
-/

namespace Collatz

/-- Aus `2^e · m^o ≤ (3m+1)^o` und `(3m+1)^q < 2^p · m^q` folgt `e/o < p/q`. -/
theorem ratio_upper {o e m q p : Nat} (ho : 0 < o) (h : 2 ^ e * m ^ o ≤ (3 * m + 1) ^ o)
    (hc : (3 * m + 1) ^ q < 2 ^ p * m ^ q) : q * e < p * o := by
  refine Nat.lt_of_not_le (fun hle => ?_)
  have h1 : (2 ^ e * m ^ o) ^ q ≤ ((3 * m + 1) ^ o) ^ q := Nat.pow_le_pow_left h q
  have h2 : ((3 * m + 1) ^ q) ^ o < (2 ^ p * m ^ q) ^ o := Nat.pow_lt_pow_left hc (by omega)
  have h3 : 2 ^ (p * o) ≤ 2 ^ (q * e) := Nat.pow_le_pow_right (by decide) hle
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at h1
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at h2
  have h4 : 2 ^ (p * o) * m ^ (q * o) ≤ 2 ^ (q * e) * m ^ (q * o) := Nat.mul_le_mul_right _ h3
  rw [Nat.mul_comm e q, Nat.mul_comm o q] at h1
  rw [Nat.mul_comm q o] at h2
  rw [Nat.mul_comm q o] at h4 h1
  omega

/-- Aus `3^o < 2^e` und `2^p < 3^q` folgt `p/q < e/o`. -/
theorem ratio_lower {o e q p : Nat} (hq : 0 < q) (h : 3 ^ o < 2 ^ e) (hc : 2 ^ p < 3 ^ q) :
    p * o < q * e := by
  refine Nat.lt_of_not_le (fun hle => ?_)
  have h1 : (3 ^ o) ^ q < (2 ^ e) ^ q := Nat.pow_lt_pow_left h (by omega)
  have h2 : (2 ^ p) ^ o ≤ (3 ^ q) ^ o := Nat.pow_le_pow_left (Nat.le_of_lt hc) o
  have h3 : 2 ^ (q * e) ≤ 2 ^ (p * o) := Nat.pow_le_pow_right (by decide) hle
  rw [← Nat.pow_mul, ← Nat.pow_mul] at h1 h2
  rw [Nat.mul_comm e q] at h1
  rw [Nat.mul_comm o q] at h1
  omega

set_option exponentiation.threshold 400000 in
/-- Kernel-Rechnung: `(3·2^24 + 1)^11611 < 2^18403 · (2^24)^11611`, d. h. `18403/11611` liegt
über `log₂ (3 + 2^-24)`. -/
theorem upper_bound_24 : (3 * 16777216 + 1) ^ 11611 < 2 ^ 18403 * 16777216 ^ 11611 := by
  decide +kernel

set_option exponentiation.threshold 2000 in
/-- `1054/665` liegt unter `log₂ 3`. -/
theorem lower_bound_24 : 2 ^ 1054 < 3 ^ 665 := by decide +kernel

/-- **Form eines weiteren Zyklus** (Eliahou-Typ): Hat ein nichttrivialer Zyklus `o` ungerade
und `e` gerade Glieder, so gibt es `a, b ≥ 1` mit `o = 665a + 11611b`, `e = 1054a + 18403b`;
seine Länge ist also `1719a + 30014b`. -/
theorem cycle_shape {n p : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ a b, 1 ≤ a ∧ 1 ≤ b ∧ oddCount n p = 665 * a + 11611 * b ∧
      evenCount n p = 1054 * a + 18403 * b ∧ p = 1719 * a + 30014 * b := by
  have hbig := nontrivial_cycle_ge_2_24 hp h0 hnt
  obtain ⟨ho, h3, hm⟩ := cycle_inequalities (m := 16777216) hp h0 hbig
  have hsum := odd_add_even n p
  have hu := ratio_upper ho hm upper_bound_24
  have hl := ratio_lower (by decide) h3 lower_bound_24
  generalize oddCount n p = o at *
  generalize evenCount n p = e at *
  refine ⟨18403 * o - 11611 * e, 665 * e - 1054 * o, by omega, by omega, by omega, by omega, by omega⟩

end Collatz
