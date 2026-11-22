import Collatz.Terras

/-!
# Fast alle Zahlen fallen ab (Terras 1976, Everett 1977)

Mit dem Satz von Terras zählen wir die Restklassen modulo `2^k` nach der Anzahl `o` ihrer
ungeraden Schritte. Die Summe `Σ_{r < 2^k} 2^o(r)` ist genau `3^k`, denn von den beiden
Hochhebungen `r` und `r + 2^k` hat genau eine im nächsten Schritt einen ungeraden Wert.

Ist `2·3^o ≤ 2^k`, so fällt jede Zahl `n ≥ 2^k` dieser Klasse nach `k` Schritten von `T`
unter `n`. Die übrigen Klassen haben viele ungerade Schritte, und davon gibt es wenige:
Ihr Anteil geht gegen 0.
-/

namespace Collatz

/-- `f 0 + f 1 + … + f (N-1)`. -/
def sumBelow (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | N + 1 => sumBelow f N + f N

/-- Anzahl der `i < N` mit `p i`. -/
def countBelow (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | N + 1 => countBelow p N + (if p N then 1 else 0)

theorem sumBelow_add (f : Nat → Nat) (N : Nat) :
    ∀ M, sumBelow f (N + M) = sumBelow f N + sumBelow (fun i => f (N + i)) M := by
  intro M
  induction M with
  | zero => rfl
  | succ M ih =>
    show sumBelow f (N + M) + f (N + M) = _ + (sumBelow (fun i => f (N + i)) M + f (N + M))
    rw [ih]; omega

theorem sumBelow_congr {f g : Nat → Nat} : ∀ N, (∀ i, i < N → f i = g i) →
    sumBelow f N = sumBelow g N := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro h
    simp only [sumBelow]
    rw [ih (fun i hi => h i (by omega)), h N (by omega)]

theorem sumBelow_add_fun (f g : Nat → Nat) : ∀ N,
    sumBelow f N + sumBelow g N = sumBelow (fun i => f i + g i) N := by
  intro N
  induction N with
  | zero => rfl
  | succ N ih => simp only [sumBelow]; omega

theorem sumBelow_mul (c : Nat) (f : Nat → Nat) : ∀ N,
    sumBelow (fun i => c * f i) N = c * sumBelow f N := by
  intro N
  induction N with
  | zero => rfl
  | succ N ih => simp only [sumBelow, ih, Nat.mul_add]

/-- Markov-Ungleichung: `#{i < N : t ≤ g i} · 2^t ≤ Σ 2^(g i)`. -/
theorem count_mul_le (t : Nat) (g : Nat → Nat) : ∀ N,
    countBelow (fun i => decide (t ≤ g i)) N * 2 ^ t ≤ sumBelow (fun i => 2 ^ g i) N := by
  intro N
  induction N with
  | zero => simp [countBelow, sumBelow]
  | succ N ih =>
    simp only [countBelow, sumBelow, Nat.add_mul]
    by_cases h : t ≤ g N
    · have : 2 ^ t ≤ 2 ^ g N := Nat.pow_le_pow_right (by decide) h
      simp only [h, decide_true, if_true, Nat.one_mul]; omega
    · have := Nat.zero_le (2 ^ g N)
      simp only [h, decide_false, Bool.false_eq_true, if_false, Nat.zero_mul, Nat.add_zero]; omega

theorem countBelow_mono {p q : Nat → Bool} (h : ∀ i, p i = true → q i = true) : ∀ N,
    countBelow p N ≤ countBelow q N := by
  intro N
  induction N with
  | zero => exact Nat.le_refl _
  | succ N ih =>
    simp only [countBelow]
    cases hp : p N
    · simp only [Bool.false_eq_true, if_false]; split <;> omega
    · simp only [if_true, h N hp]; omega

/-! ## Die Summe `Σ 2^o = 3^k` -/

theorem oddsT_eq_count : ∀ k n, oddsT k n = (parVec k n).count true := by
  intro k
  induction k with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    simp only [oddsT, parVec, List.count_cons, ih]
    by_cases h : n % 2 = 1 <;> simp [h] <;> omega

theorem oddsT_add (k r a : Nat) : oddsT k (r + 2 ^ k * a) = oddsT k r := by
  rw [oddsT_eq_count, oddsT_eq_count, (affine k r a).2]

theorem oddsT_succ : ∀ k n, oddsT (k + 1) n = oddsT k n + (if Titer k n % 2 = 1 then 1 else 0) := by
  intro k
  induction k with
  | zero => intro n; simp [oddsT, Titer]
  | succ k ih =>
    intro n
    have h := ih (T n)
    simp only [oddsT] at h ⊢
    simp only [Titer]
    rw [h]; omega

theorem three_pow_odd : ∀ o, 3 ^ o % 2 = 1 := by
  intro o
  induction o with
  | zero => rfl
  | succ o ih => rw [Nat.pow_succ]; omega

/-- Genau eine der beiden Hochhebungen `r`, `r + 2^k` hat im Schritt `k+1` einen ungeraden Wert. -/
theorem pair_sum (k r : Nat) :
    2 ^ oddsT (k + 1) r + 2 ^ oddsT (k + 1) (r + 2 ^ k) = 3 * 2 ^ oddsT k r := by
  have ha := (affine k r 1).1
  rw [Nat.mul_one] at ha
  have ho : oddsT k (r + 2 ^ k) = oddsT k r := by
    have := oddsT_add k r 1; rwa [Nat.mul_one] at this
  rw [oddsT_succ, oddsT_succ, ho, ha, Nat.mul_one]
  have h3 := three_pow_odd (oddsT k r)
  by_cases h : Titer k r % 2 = 1
  · have : ¬ (Titer k r + 3 ^ oddsT k r) % 2 = 1 := by omega
    rw [if_pos h, if_neg this]; simp only [Nat.add_zero, Nat.pow_succ]; omega
  · have : (Titer k r + 3 ^ oddsT k r) % 2 = 1 := by omega
    rw [if_neg h, if_pos this]; simp only [Nat.add_zero, Nat.pow_succ]; omega

/-- **`Σ_{r < 2^k} 2^o(r) = 3^k`.** -/
theorem sum_two_pow_odds : ∀ k, sumBelow (fun r => 2 ^ oddsT k r) (2 ^ k) = 3 ^ k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ 2 k, Nat.mul_two, sumBelow_add, sumBelow_add_fun]
    rw [sumBelow_congr (g := fun r => 3 * 2 ^ oddsT k r) (2 ^ k) (fun r _ => by
      rw [Nat.add_comm (2 ^ k) r]; exact pair_sum k r)]
    rw [sumBelow_mul, ih, Nat.pow_succ, Nat.mul_comm]

/-! ## Abstieg bei wenigen ungeraden Schritten -/

theorem cT_bound : ∀ k n, cT k n + 3 ^ oddsT k n ≤ 3 ^ oddsT k n * 2 ^ k := by
  intro k
  induction k with
  | zero => intro n; simp [cT, oddsT]
  | succ k ih =>
    intro n
    have h := ih (T n)
    simp only [cT, oddsT]
    generalize hX : 3 ^ oddsT k (T n) = X at h
    generalize cT k (T n) = c at h ⊢
    have hY : 1 ≤ 2 ^ k := Nat.pow_pos (by decide)
    by_cases hn : n % 2 = 1
    · rw [if_pos hn, if_pos hn, Nat.add_comm 1, Nat.pow_succ, hX, Nat.pow_succ]
      have : X ≤ X * 2 ^ k := Nat.le_mul_of_pos_right X hY
      rw [show X * 3 * (2 ^ k * 2) = 6 * (X * 2 ^ k) by
        rw [Nat.mul_comm X 3, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc, Nat.mul_left_comm X 2,
          ← Nat.mul_assoc, ← Nat.mul_assoc]]
      omega
    · rw [if_neg hn, if_neg hn, Nat.zero_add, Nat.zero_add, hX, Nat.pow_succ]
      rw [show X * (2 ^ k * 2) = 2 * (X * 2 ^ k) by
        rw [Nat.mul_comm (2 ^ k) 2, Nat.mul_left_comm]]
      omega

/-- **Wenige ungerade Schritte ⇒ Abstieg**: Ist `2·3^o ≤ 2^k` (mit `o` ungeraden unter den
ersten `k` Schritten von `n`) und `n ≥ 2^k`, so fällt `n` unter sich selbst. -/
theorem descends_of_few_odds {k n : Nat} (hn : 2 ^ k ≤ n) (ho : 2 * 3 ^ oddsT k n ≤ 2 ^ k) :
    Descends n := by
  refine ⟨k + oddsT k n, ?_⟩
  rw [← Titer_eq_iter]
  have hf := Titer_formula k n
  have hc := cT_bound k n
  have hX : 1 ≤ 3 ^ oddsT k n := Nat.pow_pos (by decide)
  generalize 3 ^ oddsT k n = X at hf hc ho hX
  generalize cT k n = c at hf hc
  have h1 : X * 2 ^ k ≤ X * n := Nat.mul_le_mul_left X hn
  have h2 : 2 * X * n ≤ 2 ^ k * n := Nat.mul_le_mul_right n ho
  have h3 : 2 ^ k * Titer k n < 2 ^ k * n := by
    rw [hf]; rw [Nat.mul_assoc] at h2; omega
  exact Nat.lt_of_mul_lt_mul_left h3

/-! ## Der Anteil der Ausnahmen geht gegen 0 -/

/-- Anzahl der Klassen `r < 2^k`, für die das Kriterium `2·3^o ≤ 2^k` nicht greift. -/
def badCount (k : Nat) : Nat := countBelow (fun r => decide (2 ^ k < 2 * 3 ^ oddsT k r)) (2 ^ k)

/-- Alle Zahlen `2^k ≤ n < 2^(k+1)` ausser höchstens `badCount k` vielen fallen ab:
genauer fällt `2^k + r` ab, sobald die Klasse `r` nicht zu den Ausnahmen gehört. -/
theorem descends_unless_bad {k r : Nat} (h : ¬ 2 ^ k < 2 * 3 ^ oddsT k r) :
    Descends (2 ^ k + r) := by
  apply descends_of_few_odds (k := k) (by omega)
  have := oddsT_add k r 1
  rw [Nat.mul_one] at this
  rw [Nat.add_comm (2 ^ k) r, this]; omega

/-- Bernoulli-artige Abschätzung `6561^u · (5 + u) ≤ 5 · 8192^u`. -/
theorem bernoulli : ∀ u, 6561 ^ u * (5 + u) ≤ 5 * 8192 ^ u := by
  intro u
  induction u with
  | zero => decide
  | succ u ih =>
    rw [Nat.pow_succ, Nat.pow_succ]
    generalize 6561 ^ u = A at ih ⊢
    generalize 8192 ^ u = B at ih ⊢
    have e1 : A * (5 + u) = 5 * A + u * A := by rw [Nat.mul_add, Nat.mul_comm A 5, Nat.mul_comm A u]
    have e2 : A * 6561 * (5 + (u + 1)) = 39366 * A + 6561 * (u * A) := by
      rw [show 5 + (u + 1) = 6 + u by omega, Nat.mul_add, Nat.mul_comm (A * 6561) u,
        Nat.mul_comm A 6561, Nat.mul_assoc, Nat.mul_left_comm u 6561 A]
      omega
    rw [e1] at ih
    rw [e2, show 5 * (B * 8192) = 8192 * (5 * B) by omega]
    omega

/-- Ausnahmen haben viele ungerade Schritte: für `k = 8u` mindestens `5u − 1`. -/
theorem bad_many_odds {u r : Nat} (hu : 1 ≤ u) (h : 2 ^ (8 * u) < 2 * 3 ^ oddsT (8 * u) r) :
    5 * u - 1 ≤ oddsT (8 * u) r := by
  apply Nat.le_of_not_lt
  intro hlt
  have h1 : 3 ^ (oddsT (8 * u) r + 2) ≤ 3 ^ (5 * u) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 3 ^ (5 * u) < 2 ^ (8 * u) := by
    rw [Nat.pow_mul, Nat.pow_mul]
    exact Nat.pow_lt_pow_left (by decide) (by omega)
  rw [Nat.pow_add] at h1
  have : (3 : Nat) ^ 2 = 9 := rfl
  omega

theorem badCount_mul_le {u : Nat} (hu : 1 ≤ u) : badCount (8 * u) * 2 ^ (5 * u - 1) ≤ 3 ^ (8 * u) := by
  have hm : badCount (8 * u) ≤
      countBelow (fun r => decide (5 * u - 1 ≤ oddsT (8 * u) r)) (2 ^ (8 * u)) :=
    countBelow_mono (fun r h => by
      simp only [decide_eq_true_eq] at h ⊢
      exact bad_many_odds hu h) _
  calc badCount (8 * u) * 2 ^ (5 * u - 1)
      ≤ countBelow (fun r => decide (5 * u - 1 ≤ oddsT (8 * u) r)) (2 ^ (8 * u)) * 2 ^ (5 * u - 1) :=
        Nat.mul_le_mul_right _ hm
    _ ≤ sumBelow (fun r => 2 ^ oddsT (8 * u) r) (2 ^ (8 * u)) := count_mul_le _ _ _
    _ = 3 ^ (8 * u) := sum_two_pow_odds _

/-- **Fast alle Zahlen fallen ab.** Für jedes `M` gilt ab `u ≥ 10M + 1`: Unter den `2^(8u)` Zahlen
`2^(8u) ≤ n < 2^(8u+1)` sind weniger als ein `M`-tel Ausnahmen; alle anderen fallen nach
`descends_unless_bad` beweisbar unter sich selbst. Der Anteil der Ausnahmen geht also gegen 0. -/
theorem almost_all_descend (M : Nat) : ∀ u, 10 * M + 1 ≤ u → M * badCount (8 * u) < 2 ^ (8 * u) := by
  intro u hu
  have hb := badCount_mul_le (u := u) (by omega)
  have hB := bernoulli u
  have e3 : 3 ^ (8 * u) = 6561 ^ u := by rw [Nat.pow_mul]
  have e2 : 2 ^ (8 * u) * 2 ^ (5 * u - 1) * 2 = 8192 ^ u := by
    rw [← Nat.pow_add, ← Nat.pow_succ]
    show 2 ^ (8 * u + (5 * u - 1) + 1) = _
    rw [show 8 * u + (5 * u - 1) + 1 = 13 * u by omega, Nat.pow_mul]
  have hA : 1 ≤ 6561 ^ u := Nat.pow_pos (by decide)
  rw [e3] at hb
  generalize badCount (8 * u) = c at hb ⊢
  generalize 2 ^ (8 * u) = Q at e2 ⊢
  generalize 2 ^ (5 * u - 1) = P at hb e2
  generalize 6561 ^ u = A at hb hB hA
  generalize 8192 ^ u = B at hB e2
  -- A·(10M+1) ≤ A·(5+u) ≤ 5B  ⇒  2M·A < B
  have h1 : A * (10 * M + 1) ≤ A * (5 + u) := Nat.mul_le_mul_left A (by omega)
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, Nat.mul_comm A M] at h1
  have hMA : M * A ≤ 10 * (M * A) := by omega
  have h2 : 2 * (M * A) < B := by omega
  have h3 : M * (c * P) ≤ M * A := Nat.mul_le_mul_left M hb
  apply Nat.lt_of_not_le
  intro hle
  have h4 : Q * P ≤ M * c * P := Nat.mul_le_mul_right P hle
  rw [Nat.mul_assoc] at h4
  omega

/-- Beispiel: Von den 256 Klassen modulo `2^8` sind 93 Ausnahmen (36 %). Der Anteil sinkt mit
`k` (Python: 15 % bei `k = 24`, 3 % bei `k = 64`, 0.06 % bei `k = 160`). -/
example : badCount 8 = 93 := by decide +kernel

end Collatz
