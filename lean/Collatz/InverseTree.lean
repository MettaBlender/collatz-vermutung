import Collatz.Basic

/-!
# Der Rückwärtsbaum ist unendlich verzweigt

Rückwärts gelesen bilden die Collatz-Folgen einen Baum mit der Wurzel 1. Hier beweisen wir
für **alle** natürlichen Zahlen `n`, wie dieser Baum über `n` aussieht:

* Über jedem `n` liegt die Kette `2n, 4n, 8n, …` (`iter_double_pow`).
* Ist `n` nicht durch 3 teilbar, so hat `n` **unendlich viele ungerade Vorfahren**: beliebig
  grosse ungerade `m`, deren Folge `n` erreicht (`infinitely_many_odd_ancestors`).
  Man nimmt `m = (2^e·n − 1)/3`, wobei `e` so gewählt wird, dass `2^e·n ≡ 4 (mod 6)`.
* Folgerung: Unendlich viele ungerade Zahlen erreichen die 1, und erreicht ein `n` mit
  `3 ∤ n` die 1, dann auch unendlich viele ungerade Zahlen über `n`.

(Vielfache von 3 sind dagegen Blätter: Ihr einziger Vorgänger ist `2n`, siehe `Tree.lean`.)
-/

namespace Collatz

/-- `e` Halbierungen führen von `2^e·n` zurück zu `n`. -/
theorem iter_double_pow : ∀ e n, iter e (2 ^ e * n) = n := by
  intro e
  induction e with
  | zero => intro n; simp
  | succ e ih =>
    intro n
    rw [iter_succ]
    have h : step (2 ^ (e + 1) * n) = 2 ^ e * n := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ e) 2, Nat.mul_assoc]
      rw [step_even (by omega)]
      omega
    rw [h, ih]

/-- Multiplikation mit `4^j` ändert den Rest modulo 3 nicht. -/
theorem four_pow_mul_mod_three : ∀ j a, (4 ^ j * a) % 3 = a % 3 := by
  intro j
  induction j with
  | zero => intro a; simp
  | succ j ih =>
    intro a
    rw [Nat.pow_succ, Nat.mul_assoc, ih]
    omega

/-- `j < 4^j`. -/
theorem lt_four_pow : ∀ j, j < 4 ^ j := by
  intro j
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Nat.pow_succ]
    omega

/-- **Unendlich viele ungerade Vorfahren.** Ist `n > 0` nicht durch 3 teilbar, so gibt es zu
jeder Schranke `B` ein ungerades `m > B`, dessen Collatz-Folge `n` erreicht. -/
theorem infinitely_many_odd_ancestors {n : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) :
    ∀ B, ∃ m k, B < m ∧ m % 2 = 1 ∧ iter k m = n := by
  intro B
  -- e₀ = 2 für n ≡ 1, e₀ = 1 für n ≡ 2 (mod 3); dann ist a = 2^e₀·n ≡ 1 (mod 3) und gerade.
  obtain ⟨e0, ha3, ha2, ha0⟩ : ∃ e0, (2 ^ e0 * n) % 3 = 1 ∧ (2 ^ e0 * n) % 2 = 0 ∧
      0 < 2 ^ e0 * n := by
    by_cases h1 : n % 3 = 1
    · exact ⟨2, by simp only [Nat.pow_succ, Nat.pow_zero]; omega,
        by simp only [Nat.pow_succ, Nat.pow_zero]; omega,
        by simp only [Nat.pow_succ, Nat.pow_zero]; omega⟩
    · exact ⟨1, by simp only [Nat.pow_succ, Nat.pow_zero]; omega,
        by simp only [Nat.pow_succ, Nat.pow_zero]; omega,
        by simp only [Nat.pow_succ, Nat.pow_zero]; omega⟩
  generalize ha : 2 ^ e0 * n = a at ha3 ha2 ha0
  -- x = 4^j · a mit j = 3B + 3 ist ≡ 4 (mod 6) und gross.
  have hj := lt_four_pow (3 * B + 3)
  generalize hJ : 4 ^ (3 * B + 3) = P at hj
  have hx3 : (P * a) % 3 = 1 := by rw [← hJ, four_pow_mul_mod_three]; exact ha3
  have hx2 : (P * a) % 2 = 0 := by
    obtain ⟨b, rfl⟩ : ∃ b, a = 2 * b := ⟨a / 2, by omega⟩
    rw [Nat.mul_left_comm]; omega
  have hxa : P ≤ P * a := Nat.le_mul_of_pos_right P ha0
  generalize hX : P * a = x at hx3 hx2 hxa
  refine ⟨(x - 1) / 3, 1 + (e0 + 2 * (3 * B + 3)), by omega, by omega, ?_⟩
  rw [iter_add]
  have hs : iter 1 ((x - 1) / 3) = x := by
    show step ((x - 1) / 3) = x
    rw [step_odd (by omega)]; omega
  rw [hs, ← hX, ← hJ, ← ha]
  generalize 3 * B + 3 = q
  have e : 4 ^ q * (2 ^ e0 * n) = 2 ^ (e0 + 2 * q) * n := by
    rw [Nat.pow_add, Nat.pow_mul, show (2 : Nat) ^ 2 = 4 from rfl]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [e, iter_double_pow]

/-- **Unendlich viele ungerade Zahlen erreichen die 1.** -/
theorem infinitely_many_odd_reach_one : ∀ B, ∃ m, B < m ∧ m % 2 = 1 ∧ ReachesOne m := by
  intro B
  obtain ⟨m, k, hB, hm, hk⟩ := infinitely_many_odd_ancestors (n := 1) (by decide) (by decide) B
  exact ⟨m, hB, hm, k, hk⟩

/-- Erreicht `n` (nicht durch 3 teilbar) die 1, so auch beliebig grosse ungerade Vorfahren
von `n`. Der Baum der Zahlen, die die 1 erreichen, verzweigt sich also an jedem solchen Knoten
unendlich oft. -/
theorem reachesOne_ancestors {n : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) (h : ReachesOne n) :
    ∀ B, ∃ m, B < m ∧ m % 2 = 1 ∧ ReachesOne m := by
  intro B
  obtain ⟨m, k, hB, hm, hk⟩ := infinitely_many_odd_ancestors h0 h3 B
  refine ⟨m, hB, hm, ?_⟩
  obtain ⟨j, hj⟩ := h
  exact ⟨k + j, by rw [iter_add, hk, hj]⟩

end Collatz
