/-!
# Collatz: Grunddefinitionen

Wir definieren die Collatz-Abbildung auf natürlichen Zahlen und formulieren die
Collatz-Vermutung. Die Vermutung selbst ist ein **offenes Problem** und wird hier
nur als Aussage (`Prop`) definiert, nicht bewiesen.
-/

namespace Collatz

/-- Ein Collatz-Schritt: `n/2` für gerade `n`, sonst `3n+1`. -/
def step (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `iter k n` ist das Ergebnis von `k` Collatz-Schritten ab `n`. -/
def iter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter k (step n)

/-- `n` erreicht irgendwann die 1. -/
def ReachesOne (n : Nat) : Prop := ∃ k, iter k n = 1

/-- **Die Collatz-Vermutung** (offen): jede positive ganze Zahl erreicht die 1. -/
def CollatzConjecture : Prop := ∀ n, 0 < n → ReachesOne n

@[simp] theorem iter_zero (n : Nat) : iter 0 n = n := rfl
@[simp] theorem iter_succ (k n : Nat) : iter (k + 1) n = iter k (step n) := rfl

theorem step_even {n : Nat} (h : n % 2 = 0) : step n = n / 2 := by
  simp [step, h]

theorem step_odd {n : Nat} (h : n % 2 = 1) : step n = 3 * n + 1 := by
  simp [step, h]

/-- Iterationen lassen sich zusammensetzen. -/
theorem iter_add (a b n : Nat) : iter (a + b) n = iter b (iter a n) := by
  induction a generalizing n with
  | zero => simp
  | succ a ih =>
    rw [Nat.add_right_comm, iter_succ, iter_succ, ih]

theorem iter_succ' (k n : Nat) : iter (k + 1) n = step (iter k n) := by
  rw [iter_add]; rfl

/-- Positive Zahlen bleiben positiv. -/
theorem step_pos {n : Nat} (h : 0 < n) : 0 < step n := by
  unfold step; split <;> omega

theorem iter_pos {n : Nat} (h : 0 < n) (k : Nat) : 0 < iter k n := by
  induction k generalizing n with
  | zero => simpa
  | succ k ih => exact ih (step_pos h)

/-- Gerade Zahlen werden im nächsten Schritt kleiner. -/
theorem step_lt_of_even {n : Nat} (h0 : 0 < n) (h : n % 2 = 0) : step n < n := by
  rw [step_even h]; omega

theorem reachesOne_one : ReachesOne 1 := ⟨0, rfl⟩

/-- Erreicht eine spätere Zahl der Folge die 1, dann auch `n`. -/
theorem reachesOne_of_iter {n k : Nat} (h : ReachesOne (iter k n)) : ReachesOne n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨k + j, by rw [iter_add]; exact hj⟩

theorem reachesOne_of_step {n : Nat} (h : ReachesOne (step n)) : ReachesOne n :=
  reachesOne_of_iter (k := 1) h

/-- Umgekehrt: Erreicht `n ≠ 1` die 1, dann auch `step n`. -/
theorem reachesOne_step {n : Nat} (hn : n ≠ 1) (h : ReachesOne n) : ReachesOne (step n) := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero => exact absurd hk hn
  | succ k => exact ⟨k, hk⟩

theorem reachesOne_double_iff (n : Nat) : ReachesOne (2 * n) ↔ ReachesOne n := by
  have hs : step (2 * n) = n := by rw [step_even (by omega)]; omega
  constructor
  · intro h
    by_cases h1 : 2 * n = 1
    · omega
    · have := reachesOne_step h1 h; rwa [hs] at this
  · intro h; exact reachesOne_of_step (by rwa [hs])

/-- **Alle Zweierpotenzen erreichen die 1.** -/
theorem reachesOne_pow_two (k : Nat) : ReachesOne (2 ^ k) := by
  induction k with
  | zero => exact reachesOne_one
  | succ k ih => rw [Nat.pow_succ, Nat.mul_comm]; exact (reachesOne_double_iff _).2 ih

end Collatz
