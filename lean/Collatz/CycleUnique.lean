import Collatz.Density

/-!
# Ein Zyklus ist durch seinen Paritätsvektor festgelegt (Böhm–Sontacchi)

Die Zyklusgleichung `n · (2^p − 3^o) = c` (Terras.lean) hat rechts eine Zahl `c`, die
nur vom Paritätsvektor abhängt. Darum gibt es zu jedem Paritätsvektor höchstens einen
Zyklus: `n = c / (2^p − 3^o)`. Insbesondere hat `T` höchstens `2^p` periodische
Startpunkte der Periode `p`, und man kann alle Zyklen einer festen Länge `p` durch
Ausprobieren aller `2^p` Paritätsvektoren finden (siehe `python/paritaetszyklen.py`).
-/

namespace Collatz

/-- Zahl der ungeraden Schritte und additiver Anteil hängen nur vom Paritätsvektor ab. -/
theorem odds_cT_of_parVec : ∀ k n m, parVec k n = parVec k m →
    oddsT k n = oddsT k m ∧ cT k n = cT k m := by
  intro k
  induction k with
  | zero => intro n m _; exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro n m h
    simp only [parVec, List.cons.injEq] at h
    obtain ⟨hp, hv⟩ := h
    obtain ⟨ho, hc⟩ := ih (T n) (T m) hv
    have hpar : (n % 2 = 1 ↔ m % 2 = 1) := by
      constructor <;> intro hx
      · have : (n % 2 == 1) = true := by simp [hx]
        rw [hp] at this; simpa using this
      · have : (m % 2 == 1) = true := by simp [hx]
        rw [← hp] at this; simpa using this
    simp only [oddsT, cT, ho, hc]
    by_cases hn : n % 2 = 1
    · have hm : m % 2 = 1 := hpar.mp hn
      simp [hn, hm]
    · have hm : ¬ m % 2 = 1 := fun hm => hn (hpar.mpr hm)
      simp [hn, hm]

/-- Auf einem Zyklus mit `n ≥ 1` gilt `3^o < 2^p`. -/
theorem cycle_three_pow_lt {n p : Nat} (hp : 0 < p) (h0 : 0 < n) (h : Titer p n = n) :
    3 ^ oddsT p n < 2 ^ p := by
  have hf := Titer_formula p n
  rw [h] at hf
  have hle : 3 ^ oddsT p n * n ≤ 2 ^ p * n := by omega
  have hle' : 3 ^ oddsT p n ≤ 2 ^ p := Nat.le_of_mul_le_mul_right hle h0
  have h3 := three_pow_odd (oddsT p n)
  have h2 : 2 ^ p % 2 = 0 := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [Nat.pow_succ]; simp
  have : 3 ^ oddsT p n ≠ 2 ^ p := by intro he; rw [he] at h3; omega
  omega

/-- **Satz 24 (Böhm–Sontacchi): Zwei Zyklen-Startpunkte mit demselben Paritätsvektor
sind gleich.** -/
theorem cycle_unique_of_parVec {n m p : Nat} (hp : 0 < p) (hn : 0 < n)
    (hcn : Titer p n = n) (hcm : Titer p m = m) (hv : parVec p n = parVec p m) : n = m := by
  obtain ⟨ho, hc⟩ := odds_cT_of_parVec p n m hv
  have en := cycle_equation hcn
  have em := cycle_equation hcm
  have hlt := cycle_three_pow_lt hp hn hcn
  rw [ho, hc] at en
  rw [ho] at hlt
  have he : n * (2 ^ p - 3 ^ oddsT p m) = m * (2 ^ p - 3 ^ oddsT p m) := by rw [en, em]
  exact Nat.eq_of_mul_eq_mul_right (by omega) he

/-- Beispiel: Der Paritätsvektor `[true, false]` gehört zum Zyklus `1 → 2 → 1`, der
Vektor `[false, true]` zum selben Zyklus ab `2`. -/
example : parVec 2 1 = [true, false] ∧ parVec 2 2 = [false, true] := by decide

end Collatz
