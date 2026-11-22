import Collatz.Counterexample

/-!
# Koeffizienten-Stoppzeit (Terras 1976)

Die **Stoppzeit** `σ(n)` ist der erste Schritt `j ≥ 1` mit `T^j(n) < n`. Die
**Koeffizienten-Stoppzeit** `τ(n)` ist der erste Schritt `j` mit `3^o < 2^j`, wobei `o` die
Zahl der ungeraden unter den ersten `j` Schritten ist. Wegen `2^j T^j(n) = 3^o n + c` mit
`c ≥ 0` gilt immer `τ(n) ≤ σ(n)`, und für grosse `n` (gegenüber `c`) gilt Gleichheit.

Terras' **Koeffizienten-Stoppzeit-Vermutung** (offen) sagt `σ(n) = τ(n)` für alle `n ≥ 2`.
Wir zeigen: Sie würde jeden weiteren Zyklus von `T` ausschliessen.
-/

namespace Collatz

/-- Jeder Abstieg `T^j(n) < n` hat `3^o < 2^j`; also `τ(n) ≤ σ(n)`. -/
theorem coeff_of_descent {n j : Nat} (h : Titer j n < n) : 3 ^ oddsT j n < 2 ^ j := by
  have f := Titer_formula j n
  have h1 : 2 ^ j * Titer j n < 2 ^ j * n := Nat.mul_lt_mul_of_pos_left h (Nat.pow_pos (by decide))
  have h2 : 3 ^ oddsT j n * n < 2 ^ j * n := by omega
  exact Nat.lt_of_mul_lt_mul_right h2

/-- Ist `3^o < 2^j` und `c < (2^j − 3^o)·n`, so ist `T^j(n) < n`. -/
theorem descent_of_coeff {n j : Nat} (h3 : 3 ^ oddsT j n < 2 ^ j)
    (hc : cT j n < (2 ^ j - 3 ^ oddsT j n) * n) : Titer j n < n := by
  have f := Titer_formula j n
  rw [Nat.sub_mul] at hc
  have hle : 3 ^ oddsT j n * n ≤ 2 ^ j * n := Nat.mul_le_mul_right n (Nat.le_of_lt h3)
  have : 2 ^ j * Titer j n < 2 ^ j * n := by omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- **Für grosse `n` stimmen die Stoppzeiten überein**: Ist `3^o < 2^j` und
`n ≥ 3^o · 2^j`, so ist `T^j(n) < n`. -/
theorem descent_of_coeff_large {n j : Nat} (h3 : 3 ^ oddsT j n < 2 ^ j)
    (hn : 3 ^ oddsT j n * 2 ^ j ≤ n) : Titer j n < n := by
  apply descent_of_coeff h3
  have hb := cT_bound j n
  have hd : 1 ≤ 2 ^ j - 3 ^ oddsT j n := by omega
  have : n ≤ (2 ^ j - 3 ^ oddsT j n) * n := Nat.le_mul_of_pos_left n hd
  have hX : 1 ≤ 3 ^ oddsT j n := Nat.pow_pos (by decide)
  omega

/-- Terras' Koeffizienten-Stoppzeit-Vermutung: Ist `j` der erste Schritt mit `3^o < 2^j`,
so ist schon `T^j(n) < n`. -/
def CoeffStoppingConjecture : Prop :=
  ∀ n j, 2 ≤ n → 3 ^ oddsT j n < 2 ^ j → (∀ i, i < j → 2 ^ i ≤ 3 ^ oddsT i n) → Titer j n < n

/-- Ein erstes `j` mit einer entscheidbaren Eigenschaft. -/
theorem exists_first (P : Nat → Prop) [DecidablePred P] :
    ∀ p, P p → ∃ j, j ≤ p ∧ P j ∧ ∀ i, i < j → ¬ P i := by
  intro p
  induction p using Nat.strongRecOn with
  | _ p ih =>
    intro hp
    by_cases h : ∃ i, i < p ∧ P i
    · obtain ⟨i, hi, hPi⟩ := h
      obtain ⟨j, hj, hPj, hmin⟩ := ih i hi hPi
      exact ⟨j, by omega, hPj, hmin⟩
    · exact ⟨p, Nat.le_refl p, hp, fun i hi hPi => h ⟨i, hi, hPi⟩⟩

/-- In einem Zyklus von `T` (Länge `p ≥ 1`, Glieder `≥ 1`) ist `3^o < 2^p`. -/
theorem T_cycle_coeff {m p : Nat} (hp : 0 < p) (hc : Titer p m = m) (hm : 1 ≤ m) :
    3 ^ oddsT p m < 2 ^ p := by
  have f := Titer_formula p m
  rw [hc] at f
  have hle : 3 ^ oddsT p m * m ≤ 2 ^ p * m := by omega
  have h3 : 3 ^ oddsT p m ≤ 2 ^ p := Nat.le_of_mul_le_mul_right hle hm
  refine Nat.lt_of_le_of_ne h3 (fun he => ?_)
  have h1 := three_pow_odd (oddsT p m)
  have h2 : 2 ^ p % 2 = 0 := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [Nat.pow_succ]; omega
  omega

/-- **Die Koeffizienten-Stoppzeit-Vermutung schliesst weitere Zyklen aus**: Gilt sie, so hat
kein Zyklus von `T` ein kleinstes Glied `m ≥ 2`. -/
theorem no_cycle_of_coeffStopping (H : CoeffStoppingConjecture) {m p : Nat} (hp : 0 < p)
    (hc : Titer p m = m) (hmin : ∀ k, m ≤ Titer k m) (h2 : 2 ≤ m) : False := by
  obtain ⟨j, _, hj, hfirst⟩ :=
    exists_first (fun j => 3 ^ oddsT j m < 2 ^ j) p (T_cycle_coeff hp hc (by omega))
  have := H m j h2 hj (fun i hi => Nat.le_of_not_lt (hfirst i hi))
  exact absurd (hmin j) (by omega)

end Collatz
