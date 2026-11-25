import Collatz.PeriodicParity

/-!
# Satz 59: Wie oft kann sich ein Paritätsblock wiederholen?

Quantitative Form von Satz 58. Wiederholt sich der Paritätsvektor der Länge `p` von `x`
in `J` aufeinanderfolgenden Blöcken, und ist `x` kein periodischer Punkt mit `T^p(x) = x`,
dann gilt `2^(p·(J−1)) ≤ max(x, T^p(x))`. Also kann eine Zahl `x`, die nicht auf einem
solchen Zyklus liegt, ein Muster der Länge `p` höchstens etwa `1 + log₂(x)/p`-mal
hintereinander wiederholen.

Beweis wie in Satz 58: `2^(pj)·(x_(j+1) − x_j) = 3^(oj)·(x_1 − x_0)` gilt für alle
`j ≤ J − 1`, also teilt `2^(p(J−1))` die Zahl `x_1 − x_0 ≠ 0`.
-/

namespace Collatz

theorem rb_linear {x : Nat → Nat} {P Q c J : Nat}
    (hx : ∀ j, j < J → P * x (j + 1) = Q * x j + c) :
    ∀ j, j < J → Q ^ j * x 0 + P ^ j * x (j + 1) = Q ^ j * x 1 + P ^ j * x j := by
  intro j
  induction j with
  | zero => intro _; simp only [Nat.pow_zero, Nat.one_mul, Nat.zero_add]; omega
  | succ j ih =>
    intro hj
    have ih := ih (by omega)
    have h1 := hx (j + 1) hj
    have h0 := hx j (by omega)
    have e1 : Q ^ (j + 1) * x 0 + P ^ (j + 1) * x (j + 1 + 1)
        = Q * (Q ^ j * x 0 + P ^ j * x (j + 1)) + P ^ j * c := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc (P ^ j) P, h1]
      grind
    have e2 : Q ^ (j + 1) * x 1 + P ^ (j + 1) * x (j + 1)
        = Q * (Q ^ j * x 1 + P ^ j * x j) + P ^ j * c := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc (P ^ j) P, h0]
      grind
    rw [e1, e2, ih]

/-- Aus `2^(pj) ∣ 3^(oj)·d` und `d ≠ 0` folgt `2^(pj) ≤ d`. -/
theorem rb_le_of_dvd {p o j d : Nat} (h : 2 ^ (p * j) ∣ 3 ^ (o * j) * d) (hd : 0 < d) :
    2 ^ (p * j) ≤ d := by
  have hc : Nat.Coprime (2 ^ (p * j)) (3 ^ (o * j)) :=
    Nat.Coprime.pow_right _ (coprime_pow_two_three _)
  exact Nat.le_of_dvd hd (hc.dvd_of_dvd_mul_left h)

/-- **Satz 59**: Hat `x` in `J ≥ 1` aufeinanderfolgenden Blöcken der Länge `p` denselben
Paritätsvektor und ist `T^p(x) ≠ x`, so ist `2^(p·(J−1)) ≤ max(x, T^p(x))`. -/
theorem repeated_block {x p J : Nat} (hJ : 1 ≤ J)
    (h : ∀ j, j < J → parVec p (Titer (j * p) x) = parVec p x)
    (hne : Titer p x ≠ x) :
    2 ^ (p * (J - 1)) ≤ max x (Titer p x) := by
  let y : Nat → Nat := fun j => Titer (j * p) x
  have hy0 : y 0 = x := by show Titer (0 * p) x = x; rw [Nat.zero_mul]; rfl
  have hy1 : y 1 = Titer p x := by show Titer (1 * p) x = _; rw [Nat.one_mul]
  have hstep : ∀ j, j < J → 2 ^ p * y (j + 1) = 3 ^ oddsT p x * y j + cT p x := by
    intro j hj
    have hf := Titer_formula p (y j)
    obtain ⟨ho, hc⟩ := pp_coeff_of_parVec p (y j) x (h j hj)
    have e : Titer p (y j) = y (j + 1) := by
      show Titer p (Titer (j * p) x) = Titer ((j + 1) * p) x
      rw [← pp_Titer_add, Nat.succ_mul]
    rw [e, ho, hc] at hf; exact hf
  obtain ⟨K, rfl⟩ : ∃ K, J = K + 1 := ⟨J - 1, by omega⟩
  have hlin := rb_linear hstep K (by omega)
  rw [← Nat.pow_mul, ← Nat.pow_mul] at hlin
  rw [hy0, hy1] at hlin
  rw [Nat.add_sub_cancel]
  generalize hA : 2 ^ (p * K) = A at hlin ⊢
  generalize hB : 3 ^ (oddsT p x * K) = B at hlin
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hd : A ∣ B * (x - Titer p x) := by
      refine ⟨y K - y (K + 1), ?_⟩
      rw [Nat.mul_sub B, Nat.mul_sub A]; omega
    have := rb_le_of_dvd (p := p) (o := oddsT p x) (j := K) (by rw [hA, hB]; exact hd) (by omega)
    rw [hA] at this
    have : x - Titer p x ≤ max x (Titer p x) := by omega
    omega
  · have hd : A ∣ B * (Titer p x - x) := by
      refine ⟨y (K + 1) - y K, ?_⟩
      rw [Nat.mul_sub B, Nat.mul_sub A]; omega
    have := rb_le_of_dvd (p := p) (o := oddsT p x) (j := K) (by rw [hA, hB]; exact hd) (by omega)
    rw [hA] at this
    have : Titer p x - x ≤ max x (Titer p x) := by omega
    omega

/-- Folgerung in der Sprache der Bahnen: Wiederholt sich ab der Stelle `m` ein Block der
Länge `p` genau `J`-mal, und ist `T^m(n)` kein Punkt eines Zyklus der Länge `p`, so ist
`2^(p(J−1)) ≤ max(T^m n, T^(m+p) n)`. -/
theorem repeated_block_orbit {n m p J : Nat} (hJ : 1 ≤ J)
    (h : ∀ j, j < J → parVec p (Titer (m + j * p) n) = parVec p (Titer m n))
    (hne : Titer (m + p) n ≠ Titer m n) :
    2 ^ (p * (J - 1)) ≤ max (Titer m n) (Titer (m + p) n) := by
  have e : ∀ k, Titer (m + k) n = Titer k (Titer m n) := fun k => pp_Titer_add m k n
  rw [e] at hne ⊢
  exact repeated_block hJ (fun j hj => by rw [← e]; exact h j hj) hne

end Collatz
