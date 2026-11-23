import Collatz.Counterexample

/-!
# Ein Gegenbeispiel hat zu jeder Zeit mindestens 63 % ungerade Schritte

`orbitMin_many_odds` (Satz 17) sagt das nur für die ersten `log₂ m` Schritte. Hier gilt es für
**alle** `k`, und für jede Art von Gegenbeispiel (divergente Folge oder weiterer Zyklus):

* **Wachstumsschranke** (`growth_bound`): Sind alle Glieder `x` der ersten `k` Schritte `≥ M`,
  so wächst jedes ungerade Glied höchstens um den Faktor `(3M+1)/(2M)`, jedes gerade fällt um
  `1/2`. Also `2^k · M^o · T^k(n) ≤ (3M+1)^o · n`.
* **Satz** (`orbitMin_density`): Fällt `m` nie unter sich selbst, dann gilt für **jedes** `k`
  `2^k · m^o ≤ (3m+1)^o`, also `o/k ≥ log 2 / log(3 + 1/m)`.
* Mit `m ≥ M` darf man `m` durch `M` ersetzen (`density_mono`).

Mit `m ≥ 2^27` (Satz 27) heisst das: unter den ersten 1000 Schritten mindestens 631 ungerade,
unter den ersten 10 000 mindestens 6310 (siehe `OrbitDensity27.lean`). Das ist die diskrete
Form eines Lemmas von Lagarias (1985) über divergente Folgen.
-/

namespace Collatz

/-- Ein Schritt: Für ungerades `x ≥ M` ist `2M · T(x) ≤ (3M+1) · x`. -/
theorem T_odd_bound {M x : Nat} (hx : x % 2 = 1) (hM : M ≤ x) : 2 * M * T x ≤ (3 * M + 1) * x := by
  unfold T
  rw [if_neg (by omega)]
  have h2 : 2 * ((3 * x + 1) / 2) = 3 * x + 1 := by omega
  have e1 : 2 * M * ((3 * x + 1) / 2) = M * (3 * x + 1) := by
    rw [Nat.mul_comm 2 M, Nat.mul_assoc, h2]
  rw [e1, Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.one_mul]
  have : M * (3 * x) = 3 * M * x := by rw [← Nat.mul_assoc, Nat.mul_comm M 3]
  omega

/-- **Wachstumsschranke.** Sind die ersten `k` Glieder `T^i(n)` alle `≥ M`, so gilt
`2^k · M^o · T^k(n) ≤ (3M+1)^o · n` mit `o = oddsT k n`. -/
theorem growth_bound (M : Nat) : ∀ k n, (∀ i, i < k → M ≤ Titer i n) →
    2 ^ k * M ^ oddsT k n * Titer k n ≤ (3 * M + 1) ^ oddsT k n * n := by
  intro k
  induction k with
  | zero => intro n _; simp [Titer, oddsT]
  | succ k ih =>
    intro n h
    have hT := ih (T n) (fun i hi => h (i + 1) (by omega))
    have hn : M ≤ n := h 0 (by omega)
    show 2 ^ (k + 1) * M ^ ((if n % 2 = 1 then 1 else 0) + oddsT k (T n)) * Titer k (T n) ≤
      (3 * M + 1) ^ ((if n % 2 = 1 then 1 else 0) + oddsT k (T n)) * n
    generalize oddsT k (T n) = o at hT ⊢
    generalize Titer k (T n) = t at hT ⊢
    by_cases hodd : n % 2 = 1
    · rw [if_pos hodd, Nat.add_comm 1 o, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]
      have hs := T_odd_bound hodd hn
      -- 2^k·2·(M^o·M)·t = 2M · (2^k M^o t) ≤ 2M · (3M+1)^o T n = (3M+1)^o · (2M T n)
      have e1 : 2 ^ k * 2 * (M ^ o * M) * t = 2 * M * (2 ^ k * M ^ o * t) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have e2 : (3 * M + 1) ^ o * (3 * M + 1) * n = (3 * M + 1) ^ o * ((3 * M + 1) * n) := by
        rw [Nat.mul_assoc]
      rw [e1, e2]
      calc 2 * M * (2 ^ k * M ^ o * t)
          ≤ 2 * M * ((3 * M + 1) ^ o * T n) := Nat.mul_le_mul_left _ hT
        _ = (3 * M + 1) ^ o * (2 * M * T n) := by
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ (3 * M + 1) ^ o * ((3 * M + 1) * n) := Nat.mul_le_mul_left _ hs
    · rw [if_neg hodd, Nat.zero_add, Nat.pow_succ]
      have hs : 2 * T n = n := by unfold T; rw [if_pos (by omega)]; omega
      have e1 : 2 ^ k * 2 * M ^ o * t = 2 * (2 ^ k * M ^ o * t) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rw [e1]
      calc 2 * (2 ^ k * M ^ o * t)
          ≤ 2 * ((3 * M + 1) ^ o * T n) := Nat.mul_le_mul_left _ hT
        _ = (3 * M + 1) ^ o * (2 * T n) := by
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ = (3 * M + 1) ^ o * n := by rw [hs]

/-- Das kleinste Glied einer Folge ist auch für `T` das kleinste. -/
theorem orbitMin_Titer {m : Nat} (hmin : IsOrbitMin m) (k : Nat) : m ≤ Titer k m := by
  rw [Titer_eq_iter]; exact hmin _

/-- **Dichte der ungeraden Schritte für alle `k`.** Fällt `m ≥ 1` nie unter sich selbst, so gilt
für jedes `k`: `2^k · m^o ≤ (3m+1)^o` mit `o = oddsT k m`. -/
theorem orbitMin_density {m : Nat} (h1 : 1 ≤ m) (hmin : IsOrbitMin m) (k : Nat) :
    2 ^ k * m ^ oddsT k m ≤ (3 * m + 1) ^ oddsT k m := by
  have hg := growth_bound m k m (fun i _ => orbitMin_Titer hmin i)
  have hk := orbitMin_Titer hmin k
  generalize oddsT k m = o at hg ⊢
  generalize Titer k m = t at hg hk
  have : 2 ^ k * m ^ o * m ≤ 2 ^ k * m ^ o * t := Nat.mul_le_mul_left _ hk
  exact Nat.le_of_mul_le_mul_right (Nat.le_trans this hg) h1

/-- Man darf `m` durch jede kleinere Schranke `M ≥ 1` ersetzen. -/
theorem density_mono {M m k o : Nat} (hM : 1 ≤ M) (hMm : M ≤ m)
    (h : 2 ^ k * m ^ o ≤ (3 * m + 1) ^ o) : 2 ^ k * M ^ o ≤ (3 * M + 1) ^ o := by
  -- (3m+1)·M ≤ (3M+1)·m, also (3m+1)^o M^o ≤ (3M+1)^o m^o
  have h1 : (3 * m + 1) * M ≤ (3 * M + 1) * m := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_assoc,
      Nat.mul_comm m M]
    omega
  have h2 : ((3 * m + 1) * M) ^ o ≤ ((3 * M + 1) * m) ^ o := Nat.pow_le_pow_left h1 o
  rw [Nat.mul_pow, Nat.mul_pow] at h2
  have hmo : 0 < m ^ o := Nat.pow_pos (by omega)
  have h3 : 2 ^ k * M ^ o * m ^ o ≤ (3 * M + 1) ^ o * m ^ o := by
    calc 2 ^ k * M ^ o * m ^ o = 2 ^ k * m ^ o * M ^ o := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ (3 * m + 1) ^ o * M ^ o := Nat.mul_le_mul_right _ h
      _ ≤ (3 * M + 1) ^ o * m ^ o := h2
  exact Nat.le_of_mul_le_mul_right h3 hmo

/-- Wenige ungerade Schritte widersprechen der Schranke: Ist `2^k · M^c > (3M+1)^c`, so hat
jedes `o` mit `2^k M^o ≤ (3M+1)^o` mindestens `o > c`. -/
theorem odds_gt_of_bound {M k c o : Nat} (hM : 1 ≤ M)
    (h : 2 ^ k * M ^ o ≤ (3 * M + 1) ^ o) (hc : (3 * M + 1) ^ c < 2 ^ k * M ^ c) : c < o := by
  apply Nat.lt_of_not_le
  intro hoc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hoc
  -- 2^k M^(o+d) ≤ (3M+1)^o M^d ≤ (3M+1)^(o+d)
  have h1 : 2 ^ k * M ^ (o + d) ≤ (3 * M + 1) ^ o * M ^ d := by
    rw [Nat.pow_add, ← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ h
  have h2 : (3 * M + 1) ^ o * M ^ d ≤ (3 * M + 1) ^ o * (3 * M + 1) ^ d :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) d)
  rw [← Nat.pow_add] at h2
  omega

end Collatz
