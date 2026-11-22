import Collatz.Terras
import Collatz.VerifiedHugeAll

/-!
# Keine 1-Zyklen mit wenigen ungeraden Schritten

Ein **1-Zyklus** (Steiner 1977) ist ein Zyklus von `T`, der aus `o` ungeraden Schritten am Stück
und danach `e` geraden Schritten besteht. Für diesen Paritätsvektor ist der additive Anteil der
Zyklusgleichung `c = 3^o − 2^o`, also

    n · (2^(o+e) − 3^o) = 3^o − 2^o.

Weil jeder weitere Zyklus nur Zahlen `≥ 2^22` enthält (Satz 13), müsste `2^(o+e)` extrem nahe
bei `3^o` liegen: `(2^(o+e) − 3^o) · 2^22 ≤ 3^o − 2^o`. Der Kernel prüft, dass das für keine
Zahl `1 ≤ o ≤ N` passiert. (Steiner hat mit der Theorie der Linearformen in Logarithmen
bewiesen, dass es überhaupt keinen nichttrivialen 1-Zyklus gibt; das geht über diese
Formalisierung hinaus.)
-/

namespace Collatz

theorem parVec_zeros : ∀ e n, parVec e n = List.replicate e false → cT e n = 0 ∧ oddsT e n = 0 := by
  intro e
  induction e with
  | zero => intro n _; exact ⟨rfl, rfl⟩
  | succ e ih =>
    intro n h
    simp only [parVec, List.replicate_succ, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hn : ¬ n % 2 = 1 := by intro hn; simp [hn] at h1
    obtain ⟨c0, o0⟩ := ih (T n) h2
    simp only [cT, oddsT, if_neg hn, c0, o0]; exact ⟨trivial, trivial⟩

theorem parVec_ones_zeros : ∀ o e n,
    parVec (o + e) n = List.replicate o true ++ List.replicate e false →
    cT (o + e) n = 3 ^ o - 2 ^ o ∧ oddsT (o + e) n = o := by
  intro o
  induction o with
  | zero => intro e n h; rw [Nat.zero_add] at h ⊢; exact parVec_zeros e n h
  | succ o ih =>
    intro e n h
    rw [show o + 1 + e = (o + e) + 1 by omega] at h ⊢
    simp only [parVec, List.replicate_succ, List.cons_append, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hn : n % 2 = 1 := by
      cases hm : n % 2 == 1 with
      | true => simpa using hm
      | false => rw [hm] at h1; exact absurd h1 (by decide)
    obtain ⟨c0, o0⟩ := ih e (T n) h2
    have hle : 2 ^ o ≤ 3 ^ o := Nat.pow_le_pow_left (by decide) o
    simp only [cT, oddsT, if_pos hn, c0, o0]
    refine ⟨?_, by omega⟩
    rw [Nat.pow_succ, Nat.pow_succ]
    omega

/-- **Gleichung eines 1-Zyklus**: `n · (2^(o+e) − 3^o) = 3^o − 2^o`. -/
theorem one_cycle_equation {o e n : Nat} (hc : Titer (o + e) n = n)
    (hv : parVec (o + e) n = List.replicate o true ++ List.replicate e false) :
    n * (2 ^ (o + e) - 3 ^ o) = 3 ^ o - 2 ^ o := by
  obtain ⟨c0, o0⟩ := parVec_ones_zeros o e n hv
  have := cycle_equation hc
  rwa [o0, c0] at this

/-- Kernel-Prüfung für `o = 1, 2, …`: Mit `T = 3^o`, `W = 2^o` und `E` der kleinsten
Zweierpotenz über `T` gilt `(E − T) · 2^22 > T − W`. -/
def oneCycleCheck : (fuel T W E : Nat) → Bool
  | 0, _, _, _ => true
  | f + 1, T, W, E =>
    let E' := if 3 * T < 2 * E then 2 * E else 4 * E
    decide (3 * T - 2 * W < (E' - 3 * T) * 4194304) && oneCycleCheck f (3 * T) (2 * W) E'

private theorem pow_le_of_lt_two_mul' {a b : Nat} (h : 2 ^ a < 2 * 2 ^ b) : 2 ^ a ≤ 2 ^ b := by
  have h' : 2 ^ a < 2 ^ (b + 1) := by rw [Nat.pow_succ, Nat.mul_comm]; exact h
  have hab : a < b + 1 := (Nat.pow_lt_pow_iff_right (by decide)).mp h'
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem oneCycleCheck_spec : ∀ f j e, 3 ^ j < 2 ^ e → 2 ^ e ≤ 2 * 3 ^ j →
    oneCycleCheck f (3 ^ j) (2 ^ j) (2 ^ e) = true →
    ∀ i, j < i → i ≤ j + f → ∀ m, 3 ^ i < 2 ^ m → 3 ^ i - 2 ^ i < (2 ^ m - 3 ^ i) * 4194304 := by
  intro f
  induction f with
  | zero => intro j e _ _ _ i h1 h2; omega
  | succ f ih =>
    intro j e hlo hhi h i hi1 hi2 m hm
    unfold oneCycleCheck at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hnow, hrest⟩ := h
    obtain ⟨e', hE', hlo', hhi'⟩ : ∃ e', (if 3 * 3 ^ j < 2 * 2 ^ e then 2 * 2 ^ e else 4 * 2 ^ e) = 2 ^ e' ∧
        3 * 3 ^ j < 2 ^ e' ∧ 2 ^ e' ≤ 2 * (3 * 3 ^ j) := by
      by_cases hc : 3 * 3 ^ j < 2 * 2 ^ e
      · refine ⟨e + 1, by rw [if_pos hc, Nat.pow_succ, Nat.mul_comm], ?_, ?_⟩ <;>
          rw [Nat.pow_succ] <;> omega
      · refine ⟨e + 2, by rw [if_neg hc, Nat.pow_add, Nat.mul_comm], ?_, ?_⟩ <;>
          rw [Nat.pow_add, show (2:Nat) ^ 2 = 4 from rfl] <;> omega
    rw [hE'] at hnow hrest
    have hT' : 3 * 3 ^ j = 3 ^ (j + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have hW' : 2 * 2 ^ j = 2 ^ (j + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hT', hW'] at hnow hrest
    rw [hT'] at hlo' hhi'
    by_cases hij : i = j + 1
    · subst hij
      have hle : 2 ^ e' ≤ 2 ^ m := pow_le_of_lt_two_mul' (by omega)
      have : (2 ^ e' - 3 ^ (j + 1)) * 4194304 ≤ (2 ^ m - 3 ^ (j + 1)) * 4194304 :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    · exact ih (j + 1) e' hlo' hhi' hrest i (by omega) (by omega) m hm

theorem oneCycleCheck_start {N : Nat} (h : oneCycleCheck N 1 1 2 = true) :
    ∀ o, 0 < o → o ≤ N → ∀ m, 3 ^ o < 2 ^ m → 3 ^ o - 2 ^ o < (2 ^ m - 3 ^ o) * 4194304 :=
  fun o h1 h2 => oneCycleCheck_spec N 0 1 (by decide) (by decide) h o h1 (by omega)

/-- Ein Zyklus von `T` ist auch ein Zyklus der Collatz-Abbildung. -/
theorem periodic_of_Titer {n p : Nat} (hp : 0 < p) (h : Titer p n = n) :
    Periodic n (p + oddsT p n) :=
  ⟨by omega, by rw [← Titer_eq_iter]; exact h⟩

/-- **Kein nichttrivialer 1-Zyklus mit höchstens `N` ungeraden Schritten**, sobald die
Kernel-Prüfung `oneCycleCheck N` besteht. -/
theorem no_one_cycle {N o e n : Nat} (hcheck : oneCycleCheck N 1 1 2 = true)
    (ho : 0 < o) (hoN : o ≤ N) (h0 : 0 < n) (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4)
    (hc : Titer (o + e) n = n)
    (hv : parVec (o + e) n = List.replicate o true ++ List.replicate e false) : False := by
  have heq := one_cycle_equation hc hv
  have hbig := nontrivial_cycle_ge_2_22 (periodic_of_Titer (by omega) hc) h0 hnt 0
  simp only [iter_zero] at hbig
  have hlt : 2 ^ o < 3 ^ o := Nat.pow_lt_pow_left (by decide) (by omega)
  by_cases hD : 3 ^ o < 2 ^ (o + e)
  · have hk := oneCycleCheck_start hcheck o ho hoN (o + e) hD
    have : 4194304 * (2 ^ (o + e) - 3 ^ o) ≤ n * (2 ^ (o + e) - 3 ^ o) :=
      Nat.mul_le_mul_right _ hbig
    rw [heq] at this
    omega
  · have : 2 ^ (o + e) - 3 ^ o = 0 := by omega
    rw [this, Nat.mul_zero] at heq
    omega

/-- Kernel-Rechnung: die Prüfung besteht für alle `o ≤ 30000`. -/
theorem oneCycleCheck_30000 : oneCycleCheck 30000 1 1 2 = true := by decide +kernel

/-- **Es gibt keinen nichttrivialen 1-Zyklus mit höchstens 30 000 ungeraden Schritten.** -/
theorem no_one_cycle_30000 {o e n : Nat} (ho : 0 < o) (hoN : o ≤ 30000) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) (hc : Titer (o + e) n = n)
    (hv : parVec (o + e) n = List.replicate o true ++ List.replicate e false) : False :=
  no_one_cycle oneCycleCheck_30000 ho hoN h0 hnt hc hv

end Collatz
