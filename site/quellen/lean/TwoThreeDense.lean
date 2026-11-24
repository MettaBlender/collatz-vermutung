import Collatz.Basic

/-!
# Satz 55: Potenzen von 2 und 3 kommen sich beliebig nahe

Für jedes `N ≥ 1` gibt es Exponenten mit `1 < 2^a / 3^b < 1 + 1/N`.

Beweis ohne Logarithmen, als „Euklid auf den Brüchen“: Man hält zwei Brüche
`x = 2^a₁/3^b₁ > 1` und `y = 3^b₂/2^a₂ > 1` und ersetzt den grösseren durch
„grösser geteilt durch kleiner“. Das bleibt `> 1` (eine Zweierpotenz ist nie eine
Dreierpotenz) und ist wieder von derselben Bauart. Wären alle solchen Brüche
mindestens `1 + 1/N`, so würde das Produkt `x·y` bei jedem Schritt um den Faktor
`N/(N+1)` kleiner. Nach `N` Schritten wäre es höchstens `2·(N/(N+1))^N ≤ 1`, obwohl `x·y > 1`.

Daraus folgt in einem zweiten Schritt auch die Form `2^a/3^b ∈ (1, 1+1/N)` selbst.
-/

namespace Collatz

/-- Bernoulli in Nat: `N^s·(N+s) ≤ N·(N+1)^s`. -/
theorem bernoulli_nat (N : Nat) : ∀ s, N ^ s * (N + s) ≤ N * (N + 1) ^ s := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.pow_succ, Nat.pow_succ]
    -- N^s*N*(N+s+1) ≤ N*((N+1)^s*(N+1))
    have h1 : N ^ s * N * (N + (s + 1)) ≤ N ^ s * (N + s) * (N + 1) := by
      have : N * (N + (s + 1)) ≤ (N + s) * (N + 1) := by
        have e1 : N * (N + (s + 1)) = N * N + N * s + N := by
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
        have e2 : (N + s) * (N + 1) = N * N + N + N * s + s := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one, Nat.mul_comm s N]
          omega
        rw [e1, e2]; omega
      calc N ^ s * N * (N + (s + 1)) = N ^ s * (N * (N + (s + 1))) := by rw [Nat.mul_assoc]
        _ ≤ N ^ s * ((N + s) * (N + 1)) := Nat.mul_le_mul_left _ this
        _ = N ^ s * (N + s) * (N + 1) := by rw [Nat.mul_assoc]
    calc N ^ s * N * (N + (s + 1)) ≤ N ^ s * (N + s) * (N + 1) := h1
      _ ≤ N * (N + 1) ^ s * (N + 1) := Nat.mul_le_mul_right _ ih
      _ = N * ((N + 1) ^ s * (N + 1)) := by rw [Nat.mul_assoc]

theorem two_pow_ne_three_pow {a b : Nat} (ha : 1 ≤ a) : 2 ^ a ≠ 3 ^ b := by
  intro h
  have h2 : 2 ^ a % 2 = 0 := by
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
    rw [Nat.pow_succ, Nat.mul_mod_left]
  have h3 : ∀ c, 3 ^ c % 2 = 1 := by
    intro c
    induction c with
    | zero => decide
    | succ c ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
  have := h3 b
  omega

/-- Ein Zustand der Euklid-Iteration: `x = 2^a₁/3^b₁ > 1`, `y = 3^b₂/2^a₂ > 1` und
`x·y·((N+1)/N)^s ≤ 2`. -/
def EState (N s a₁ b₁ a₂ b₂ : Nat) : Prop :=
  3 ^ b₁ < 2 ^ a₁ ∧ 2 ^ a₂ < 3 ^ b₂ ∧
    2 ^ a₁ * 3 ^ b₂ * (N + 1) ^ s ≤ 2 * (3 ^ b₁ * 2 ^ a₂) * N ^ s

theorem estate_step {N s a₁ b₁ a₂ b₂ : Nat} (h : EState N s a₁ b₁ a₂ b₂)
    (Hx : ∀ a b, 3 ^ b < 2 ^ a → (N + 1) * 3 ^ b ≤ N * 2 ^ a)
    (Hy : ∀ a b, 2 ^ a < 3 ^ b → (N + 1) * 2 ^ a ≤ N * 3 ^ b) :
    ∃ a₁' b₁' a₂' b₂', EState N (s + 1) a₁' b₁' a₂' b₂' := by
  obtain ⟨hx, hy, hI⟩ := h
  have ha1 : 1 ≤ a₁ := by
    rcases Nat.eq_zero_or_pos a₁ with h0 | h0
    · subst h0; have := Nat.one_le_pow b₁ 3 (by decide); rw [Nat.pow_zero] at hx; omega
    · exact h0
  by_cases hc : 3 ^ b₁ * 3 ^ b₂ < 2 ^ a₁ * 2 ^ a₂
  · -- x > y: ersetze x durch x/y = 2^(a₁+a₂)/3^(b₁+b₂)
    refine ⟨a₁ + a₂, b₁ + b₂, a₂, b₂, ?_, hy, ?_⟩
    · rw [Nat.pow_add 2 a₁ a₂, Nat.pow_add 3 b₁ b₂]; exact hc
    · have hY := Hy a₂ b₂ hy
      rw [Nat.pow_add 2 a₁ a₂, Nat.pow_add 3 b₁ b₂, Nat.pow_succ (N + 1) s, Nat.pow_succ N s]
      -- (2^a₁*2^a₂)*3^b₂*((N+1)^s*(N+1)) ≤ 2*(3^b₁*3^b₂*2^a₂)*(N^s*N)
      calc 2 ^ a₁ * 2 ^ a₂ * 3 ^ b₂ * ((N + 1) ^ s * (N + 1))
          = (2 ^ a₁ * 3 ^ b₂ * (N + 1) ^ s) * ((N + 1) * 2 ^ a₂) := by
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ (2 * (3 ^ b₁ * 2 ^ a₂) * N ^ s) * (N * 3 ^ b₂) := Nat.mul_le_mul hI hY
        _ = 2 * (3 ^ b₁ * 3 ^ b₂ * 2 ^ a₂) * (N ^ s * N) := by
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  · -- y ≥ x, sogar y > x: ersetze y durch y/x = 3^(b₂+b₁)/2^(a₂+a₁)
    have hne : 3 ^ b₁ * 3 ^ b₂ ≠ 2 ^ a₁ * 2 ^ a₂ := by
      rw [← Nat.pow_add, ← Nat.pow_add]
      exact fun e => two_pow_ne_three_pow (a := a₁ + a₂) (b := b₁ + b₂) (by omega) e.symm
    have hc' : 2 ^ a₁ * 2 ^ a₂ < 3 ^ b₁ * 3 ^ b₂ := by omega
    refine ⟨a₁, b₁, a₁ + a₂, b₁ + b₂, hx, ?_, ?_⟩
    · rw [Nat.pow_add 2 a₁ a₂, Nat.pow_add 3 b₁ b₂]; exact hc'
    · have hX := Hx a₁ b₁ hx
      rw [Nat.pow_add 2 a₁ a₂, Nat.pow_add 3 b₁ b₂, Nat.pow_succ (N + 1) s, Nat.pow_succ N s]
      calc 2 ^ a₁ * (3 ^ b₁ * 3 ^ b₂) * ((N + 1) ^ s * (N + 1))
          = (2 ^ a₁ * 3 ^ b₂ * (N + 1) ^ s) * ((N + 1) * 3 ^ b₁) := by
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ (2 * (3 ^ b₁ * 2 ^ a₂) * N ^ s) * (N * 2 ^ a₁) := Nat.mul_le_mul hI hX
        _ = 2 * (3 ^ b₁ * (2 ^ a₁ * 2 ^ a₂)) * (N ^ s * N) := by
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem estate_all {N : Nat}
    (Hx : ∀ a b, 3 ^ b < 2 ^ a → (N + 1) * 3 ^ b ≤ N * 2 ^ a)
    (Hy : ∀ a b, 2 ^ a < 3 ^ b → (N + 1) * 2 ^ a ≤ N * 3 ^ b) :
    ∀ s, ∃ a₁ b₁ a₂ b₂, EState N s a₁ b₁ a₂ b₂ := by
  intro s
  induction s with
  | zero => exact ⟨2, 1, 1, 1, by decide, by decide, by simp⟩
  | succ s ih =>
    obtain ⟨a₁, b₁, a₂, b₂, h⟩ := ih
    exact estate_step h Hx Hy

/-- **Satz 55 (Form A).** Für jedes `N ≥ 1` liegt ein Bruch `2^a/3^b` oder `3^b/2^a`
echt zwischen `1` und `1 + 1/N`. -/
theorem two_three_close (N : Nat) (hN : 1 ≤ N) :
    (∃ a b, 3 ^ b < 2 ^ a ∧ N * 2 ^ a < (N + 1) * 3 ^ b) ∨
    (∃ a b, 2 ^ a < 3 ^ b ∧ N * 3 ^ b < (N + 1) * 2 ^ a) := by
  apply Classical.byContradiction
  intro hno
  have Hx : ∀ a b, 3 ^ b < 2 ^ a → (N + 1) * 3 ^ b ≤ N * 2 ^ a := by
    intro a b h
    apply Classical.byContradiction; intro h'
    exact hno (Or.inl ⟨a, b, h, by omega⟩)
  have Hy : ∀ a b, 2 ^ a < 3 ^ b → (N + 1) * 2 ^ a ≤ N * 3 ^ b := by
    intro a b h
    apply Classical.byContradiction; intro h'
    exact hno (Or.inr ⟨a, b, h, by omega⟩)
  obtain ⟨a₁, b₁, a₂, b₂, hx, hy, hI⟩ := estate_all Hx Hy N
  -- P > Q, aber P·(N+1)^N ≤ 2·Q·N^N ≤ Q·(N+1)^N
  have hB := bernoulli_nat N N
  have hPQ : 3 ^ b₁ * 2 ^ a₂ < 2 ^ a₁ * 3 ^ b₂ := Nat.mul_lt_mul'' hx hy
  have h2 : 2 * N ^ N ≤ (N + 1) ^ N := by
    have : N ^ N * (2 * N) ≤ N * (N + 1) ^ N := by rw [Nat.two_mul]; exact hB
    have : N * (2 * N ^ N) ≤ N * (N + 1) ^ N := by
      calc N * (2 * N ^ N) = N ^ N * (2 * N) := by
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ N * (N + 1) ^ N := this
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hpos : 0 < (N + 1) ^ N := Nat.pow_pos (by omega)
  have : 2 ^ a₁ * 3 ^ b₂ * (N + 1) ^ N ≤ 3 ^ b₁ * 2 ^ a₂ * (N + 1) ^ N :=
    calc 2 ^ a₁ * 3 ^ b₂ * (N + 1) ^ N ≤ 2 * (3 ^ b₁ * 2 ^ a₂) * N ^ N := hI
      _ = 3 ^ b₁ * 2 ^ a₂ * (2 * N ^ N) := by
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 3 ^ b₁ * 2 ^ a₂ * (N + 1) ^ N := Nat.mul_le_mul_left _ h2
  have := Nat.le_of_mul_le_mul_right this hpos
  omega

theorem two_mul_pow_ne {m a c : Nat} : 2 * 2 ^ (m * a) ≠ 3 ^ c := by
  intro h
  have : 2 ^ (m * a + 1) = 3 ^ c := by rw [Nat.pow_succ, Nat.mul_comm]; exact h
  exact two_pow_ne_three_pow (by omega) this

/-- Irgendwann überholt `3^(Mb)` die Zahl `2·2^(Ma)`, wenn `2^a < 3^b`. -/
theorem three_overtakes {a b : Nat} (h : 2 ^ a < 3 ^ b) :
    2 * 2 ^ ((2 ^ a + 1) * a) < 3 ^ ((2 ^ a + 1) * b) := by
  generalize hu : 2 ^ a = u at h
  have hu0 : 0 < u := by rw [← hu]; exact Nat.two_pow_pos a
  have hB := bernoulli_nat u (u + 1)
  -- (u+1)^(u+1) > 2 u^(u+1)
  have h1 : 2 * u ^ (u + 1) < (u + 1) ^ (u + 1) := by
    have : u * (2 * u ^ (u + 1)) < u * (u + 1) ^ (u + 1) := by
      calc u * (2 * u ^ (u + 1)) < u ^ (u + 1) * (u + (u + 1)) := by
            have hp : 0 < u ^ (u + 1) := Nat.pow_pos hu0
            rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
            have : u * (2 * u ^ (u + 1)) = u ^ (u + 1) * u + u ^ (u + 1) * u := by
              rw [Nat.mul_comm u, Nat.two_mul, Nat.add_mul]
            omega
        _ ≤ u * (u + 1) ^ (u + 1) := hB
    exact Nat.lt_of_mul_lt_mul_left this
  have h2 : (u + 1) ^ (u + 1) ≤ (3 ^ b) ^ (u + 1) := Nat.pow_le_pow_left h _
  rw [Nat.mul_comm (u + 1) a, Nat.mul_comm (u + 1) b, Nat.pow_mul, Nat.pow_mul, hu]
  omega

theorem last_below {a b : Nat} : ∀ M, 2 * 2 ^ (M * a) < 3 ^ (M * b) →
    ∃ m, 3 ^ (m * b) < 2 * 2 ^ (m * a) ∧ 2 * 2 ^ ((m + 1) * a) < 3 ^ ((m + 1) * b) := by
  intro M
  induction M with
  | zero => intro h; simp at h
  | succ M ih =>
    intro h
    by_cases hM : 2 * 2 ^ (M * a) < 3 ^ (M * b)
    · exact ih hM
    · exact ⟨M, by have := @two_mul_pow_ne M a (M * b); omega, h⟩

/-- **Satz 55.** Für jedes `N ≥ 1` gibt es `a, b` mit `1 < 2^a/3^b < 1 + 1/N`. -/
theorem two_three_dense (N : Nat) (hN : 1 ≤ N) :
    ∃ a b, 3 ^ b < 2 ^ a ∧ N * 2 ^ a < (N + 1) * 3 ^ b := by
  rcases two_three_close N hN with hx | ⟨a, b, hy, hyN⟩
  · exact hx
  · obtain ⟨m, hlo, hhi⟩ := last_below (2 ^ a + 1) (three_overtakes hy)
    refine ⟨m * a + 1, m * b, by rw [Nat.pow_succ, Nat.mul_comm (2 ^ (m * a))]; exact hlo, ?_⟩
    -- X = 2·2^(ma), Y = 3^(mb): X·2^a < Y·3^b und N·3^b < (N+1)·2^a
    rw [show (m + 1) * a = m * a + a from Nat.succ_mul m a,
      show (m + 1) * b = m * b + b from Nat.succ_mul m b, Nat.pow_add, Nat.pow_add] at hhi
    have hpos : 0 < 2 ^ a := Nat.two_pow_pos a
    have key : N * (2 * 2 ^ (m * a)) * 2 ^ a < (N + 1) * 3 ^ (m * b) * 2 ^ a :=
      calc N * (2 * 2 ^ (m * a)) * 2 ^ a = N * (2 * (2 ^ (m * a) * 2 ^ a)) := by
            rw [Nat.mul_assoc, Nat.mul_assoc]
        _ ≤ N * (3 ^ (m * b) * 3 ^ b) := Nat.mul_le_mul_left _ (Nat.le_of_lt hhi)
        _ = 3 ^ (m * b) * (N * 3 ^ b) := by
            rw [Nat.mul_comm (3 ^ (m * b)) (3 ^ b), ← Nat.mul_assoc, Nat.mul_comm]
        _ < 3 ^ (m * b) * ((N + 1) * 2 ^ a) :=
            Nat.mul_lt_mul_of_pos_left hyN (Nat.pow_pos (by decide))
        _ = (N + 1) * 3 ^ (m * b) * 2 ^ a := by
            rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ (m * b)) (N + 1)]
    have := Nat.lt_of_mul_lt_mul_right key
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ (m * a)) 2]
    exact this

end Collatz
