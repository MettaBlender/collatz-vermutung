import Collatz.Counterexample
import Collatz.InverseTree

/-!
# Gegenbeispiele liessen sich nicht durch Restklassen einsperren

**Satz** (`ancestor_in_class`): Ist `n > 0` nicht durch 3 teilbar, so hat `n` in **jeder**
Restklasse modulo `2^k` einen Vorfahren `m` (eine Zahl, deren Folge `n` erreicht).

Folgerungen, beide für alle `k`:

* `reachesOne_in_every_class`: Jede Restklasse modulo `2^k` enthält Zahlen, die die 1 erreichen.
* `counterexample_in_every_class`: Gäbe es ein Gegenbeispiel, dann gäbe es eines in **jeder**
  Restklasse modulo `2^k`. Keine Aussage der Form „Gegenbeispiele liegen nur in den Klassen …“
  kann also stimmen, das Sieb kann nie ganze Klassen ausschliessen. (Satz 9 sagt dasselbe für
  „fällt in `k` Schritten“; hier geht es um die Vermutung selbst.)
* `conjecture_iff_class`: Umgekehrt genügt es, die Vermutung für **eine einzige** Restklasse
  modulo `2^k` zu beweisen, etwa nur für `n ≡ 1 (mod 2^100)`.

Zutaten:

1. **2 ist Primitivwurzel modulo `3^J`** (`two_pow_hits`): Für `3 ∤ n`, `3 ∤ y` gibt es `m`, `b`
   mit `2^m · n = y + 3^J · b`. Über `4^(3^j) = 1 + 3^(j+1)·w` mit `w ≡ 1 (mod 3)` (`four_lift`):
   Multiplikation mit `4^(3^j)` erhöht den Quotienten modulo 3 um `y`, also trifft man nach
   höchstens zwei Schritten die nächste Dreierpotenz.
2. Die affine Formel von Terras `T^k(s + 2^k b) = T^k(s) + 3^o b`, und `3 ∤ T^k(s)` für `o ≥ 1`.
-/

namespace Collatz

/-- **Hebung.** `4^(3^j) = 1 + 3^(j+1)·w` mit `w ≡ 1 (mod 3)`. -/
theorem four_lift : ∀ j, ∃ w, w % 3 = 1 ∧ 4 ^ (3 ^ j) = 1 + 3 ^ (j + 1) * w := by
  intro j
  induction j with
  | zero => exact ⟨1, rfl, rfl⟩
  | succ j ih =>
    obtain ⟨w, hw, h⟩ := ih
    have hpow : 4 ^ (3 ^ (j + 1)) = (4 ^ (3 ^ j)) ^ 3 := by
      rw [Nat.pow_succ, Nat.pow_mul]
    have e1 : 3 ^ (j + 1) = 3 * 3 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
    have e2 : 3 ^ (j + 1 + 1) = 9 * 3 ^ j := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]
    rw [hpow, h, e1, e2]
    generalize 3 ^ j = D
    refine ⟨w + 3 * (D * (w * w)) + 3 * (D * (D * (w * (w * w)))), by omega, ?_⟩
    grind

/-- Ein Schritt: Multiplikation mit `4^(3^j) = 1 + M w` erhöht den Quotienten um `y` modulo 3. -/
theorem bump {j n y a q : Nat} (h : 4 ^ a * n = y + 3 ^ (j + 1) * q) :
    ∃ q', 4 ^ (a + 3 ^ j) * n = y + 3 ^ (j + 1) * q' ∧ q' % 3 = (q + y) % 3 := by
  obtain ⟨w, hw, hP⟩ := four_lift j
  generalize hM : 3 ^ (j + 1) = M at h hP
  have hM3 : M % 3 = 0 := by
    rw [← hM, Nat.pow_succ]; exact Nat.mul_mod_left _ 3
  refine ⟨q + y * w + M * (q * w), ?_, ?_⟩
  · rw [Nat.pow_add, Nat.mul_right_comm, h, hP]
    grind
  · have h1 : (y * w) % 3 = y % 3 := by rw [Nat.mul_mod, hw, Nat.mul_one, Nat.mod_mod]
    have h2 : (M * (q * w)) % 3 = 0 := by rw [Nat.mul_mod, hM3, Nat.zero_mul, Nat.zero_mod]
    omega

/-- **Primitivwurzel, gerader Teil.** Für `n ≡ y ≢ 0 (mod 3)` gibt es `a`, `q` mit
`4^a · n = y + 3^(j+1) · q`. -/
theorem four_pow_hits : ∀ j n y, n % 3 = y % 3 → y % 3 ≠ 0 → 0 < n →
    ∃ a q, 4 ^ a * n = y + 3 ^ (j + 1) * q := by
  intro j
  induction j with
  | zero =>
    intro n y hny hy hn
    have hl := lt_four_pow y
    have hm := four_pow_mul_mod_three y n
    have : 4 ^ y ≤ 4 ^ y * n := Nat.le_mul_of_pos_right _ hn
    exact ⟨y, (4 ^ y * n - y) / 3, by rw [Nat.pow_one]; omega⟩
  | succ j ih =>
    intro n y hny hy hn
    obtain ⟨a, q, h⟩ := ih n y hny hy hn
    have fin : ∀ a q, 4 ^ a * n = y + 3 ^ (j + 1) * q → q % 3 = 0 →
        ∃ a q, 4 ^ a * n = y + 3 ^ (j + 1 + 1) * q := by
      intro a q h hq
      obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t := ⟨q / 3, by omega⟩
      refine ⟨a, t, ?_⟩
      rw [h, Nat.pow_succ 3 (j + 1), Nat.mul_assoc]
    obtain ⟨q1, h1, e1⟩ := bump h
    obtain ⟨q2, h2, e2⟩ := bump h1
    by_cases c0 : q % 3 = 0
    · exact fin a q h c0
    by_cases c1 : q1 % 3 = 0
    · exact fin _ q1 h1 c1
    have c2 : q2 % 3 = 0 := by
      clear h h1 h2 fin ih hny hn
      have hq1 : q1 % 3 = (q % 3 + y % 3) % 3 := by rw [e1, Nat.add_mod]
      rw [e2, Nat.add_mod, hq1]
      rw [hq1] at c1
      have ha : q % 3 = 1 ∨ q % 3 = 2 := by omega
      have hb : y % 3 = 1 ∨ y % 3 = 2 := by omega
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] at c1 ⊢ <;>
        first | rfl | exact absurd rfl c1
    exact fin _ q2 h2 c2

/-- **2 ist Primitivwurzel modulo `3^J`.** Für `3 ∤ n`, `3 ∤ y` gibt es `m`, `b` mit
`2^m · n = y + 3^J · b`. -/
theorem two_pow_hits (J n y : Nat) (hn : n % 3 ≠ 0) (hy : y % 3 ≠ 0) (h0 : 0 < n) :
    ∃ m b, 2 ^ m * n = y + 3 ^ J * b := by
  cases J with
  | zero =>
    have hl : y < 2 ^ y := Nat.lt_two_pow_self
    have : 2 ^ y ≤ 2 ^ y * n := Nat.le_mul_of_pos_right _ h0
    exact ⟨y, 2 ^ y * n - y, by rw [Nat.pow_zero, Nat.one_mul]; omega⟩
  | succ j =>
    by_cases hc : n % 3 = y % 3
    · obtain ⟨a, q, h⟩ := four_pow_hits j n y hc hy h0
      exact ⟨2 * a, q, by rw [Nat.pow_mul]; exact h⟩
    · obtain ⟨a, q, h⟩ := four_pow_hits j (2 * n) y (by omega) hy (by omega)
      refine ⟨2 * a + 1, q, ?_⟩
      rw [Nat.pow_succ, Nat.pow_mul, Nat.mul_assoc, Nat.mul_comm 2 n, ← Nat.mul_assoc,
        Nat.mul_assoc _ n 2, Nat.mul_comm n 2]
      exact h

/-- `m` Halbierungen unter `T`: `T^m(2^m · n) = n`. -/
theorem Titer_two_pow : ∀ m n, Titer m (2 ^ m * n) = n := by
  intro m
  induction m with
  | zero => intro n; simp [Titer]
  | succ m ih =>
    intro n
    show Titer m (T (2 ^ (m + 1) * n)) = n
    have : T (2 ^ (m + 1) * n) = 2 ^ m * n := by
      unfold T
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2, Nat.mul_assoc, if_pos (by omega)]
      omega
    rw [this, ih]

/-- Nach gerade Schritten bleibt `3 ∤ x` erhalten. -/
theorem Titer_mod_three_even : ∀ k x, oddsT k x = 0 → x % 3 ≠ 0 → Titer k x % 3 ≠ 0 := by
  intro k
  induction k with
  | zero => intro x _ hx; exact hx
  | succ k ih =>
    intro x ho hx
    simp only [oddsT] at ho
    have hev : x % 2 = 0 := by
      by_cases h : x % 2 = 1
      · rw [if_pos h] at ho; omega
      · omega
    rw [if_neg (by omega), Nat.zero_add] at ho
    show Titer k (T x) % 3 ≠ 0
    apply ih _ ho
    unfold T; rw [if_pos hev]; omega

/-- Nach mindestens einem ungeraden Schritt ist `T^k(r)` nicht durch 3 teilbar. -/
theorem Titer_mod_three : ∀ k r, 1 ≤ oddsT k r → Titer k r % 3 ≠ 0 := by
  intro k
  induction k with
  | zero => intro r h; simp [oddsT] at h
  | succ k ih =>
    intro r h
    show Titer k (T r) % 3 ≠ 0
    by_cases ho : 1 ≤ oddsT k (T r)
    · exact ih _ ho
    · have h0 : oddsT k (T r) = 0 := by omega
      simp only [oddsT, h0, Nat.add_zero] at h
      have hodd : r % 2 = 1 := by
        by_cases hr : r % 2 = 1
        · exact hr
        · rw [if_neg hr] at h; omega
      apply Titer_mod_three_even k _ h0
      unfold T; rw [if_neg (by omega)]; omega

/-- **Satz.** Ist `n > 0` nicht durch 3 teilbar, so gibt es in jeder Restklasse `s` modulo
`2^k` ein `m`, dessen `T`-Folge `n` erreicht. -/
theorem ancestor_in_class_T {n : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) (k s : Nat) :
    ∃ m j, m % 2 ^ k = s % 2 ^ k ∧ Titer j m = n := by
  generalize hs' : s % 2 ^ k = s'
  have hlt : s' < 2 ^ k := by rw [← hs']; exact Nat.mod_lt _ (Nat.two_pow_pos k)
  -- T^k(s' + 2^k b) = y + 3^o b
  have key : ∀ m b, 2 ^ m * n = Titer k s' + 3 ^ oddsT k s' * b →
      ∃ m j, m % 2 ^ k = s' ∧ Titer j m = n := by
    intro m b h
    refine ⟨s' + 2 ^ k * b, k + m, ?_, ?_⟩
    · rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hlt
    · rw [Titer_add, (affine k s' b).1, ← h, Titer_two_pow]
  by_cases ho : oddsT k s' = 0
  · have hl : Titer k s' < 2 ^ Titer k s' := Nat.lt_two_pow_self
    have : 2 ^ Titer k s' ≤ 2 ^ Titer k s' * n := Nat.le_mul_of_pos_right _ h0
    exact key (Titer k s') (2 ^ Titer k s' * n - Titer k s')
      (by rw [ho, Nat.pow_zero, Nat.one_mul]; omega)
  · obtain ⟨m, b, h⟩ := two_pow_hits (oddsT k s') n (Titer k s') h3
      (Titer_mod_three k s' (by omega)) h0
    exact key m b h

/-- Erreicht `x` die 1, so auch `step x`. -/
theorem reachesOne_step' {x : Nat} (h : ReachesOne x) : ReachesOne (step x) := by
  by_cases hx : x = 1
  · subst hx; exact ⟨2, rfl⟩
  · exact reachesOne_step hx h

theorem reachesOne_iter {x : Nat} (h : ReachesOne x) : ∀ i, ReachesOne (iter i x) := by
  intro i
  induction i generalizing x with
  | zero => exact h
  | succ i ih => rw [iter_succ]; exact ih (reachesOne_step' h)

/-- **Satz (Vorfahren in jeder Klasse).** -/
theorem ancestor_in_class {n : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) (k s : Nat) :
    ∃ m i, m % 2 ^ k = s % 2 ^ k ∧ iter i m = n := by
  obtain ⟨m, j, hm, hj⟩ := ancestor_in_class_T h0 h3 k s
  exact ⟨m, j + oddsT j m, hm, by rw [← Titer_eq_iter]; exact hj⟩

/-- **Jede Restklasse modulo `2^k` enthält Zahlen, die die 1 erreichen.** -/
theorem reachesOne_in_every_class (k s : Nat) : ∃ m, m % 2 ^ k = s % 2 ^ k ∧ ReachesOne m := by
  obtain ⟨m, i, hm, hi⟩ := ancestor_in_class (n := 1) (by decide) (by decide) k s
  exact ⟨m, hm, i, hi⟩

/-- Ein Gegenbeispiel liefert eines, das nicht durch 3 teilbar ist. -/
theorem counterexample_not_three : ∀ n, 0 < n → ¬ ReachesOne n →
    ∃ n', 0 < n' ∧ n' % 3 ≠ 0 ∧ ¬ ReachesOne n' := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro h0 h
    by_cases h3 : n % 3 = 0
    · by_cases h2 : n % 2 = 0
      · have hs : step n = n / 2 := step_even h2
        exact ih (n / 2) (by omega) (by omega)
          (fun hr => h (reachesOne_of_step (by rw [hs]; exact hr)))
      · have hs : step n = 3 * n + 1 := step_odd (by omega)
        exact ⟨3 * n + 1, by omega, by omega,
          fun hr => h (reachesOne_of_step (by rw [hs]; exact hr))⟩
    · exact ⟨n, h0, h3, h⟩

/-- **Gäbe es ein Gegenbeispiel, dann gäbe es eines in jeder Restklasse modulo `2^k`.** -/
theorem counterexample_in_every_class (h : ¬ CollatzConjecture) (k s : Nat) :
    ∃ m, 0 < m ∧ m % 2 ^ k = s % 2 ^ k ∧ ¬ ReachesOne m := by
  have : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact h (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  obtain ⟨n, hn, hr⟩ := this
  obtain ⟨n', hn', h3, hr'⟩ := counterexample_not_three n hn hr
  obtain ⟨m, i, hm, hi⟩ := ancestor_in_class hn' h3 k s
  refine ⟨m, ?_, hm, fun hm1 => hr' (hi ▸ reachesOne_iter hm1 i)⟩
  apply Nat.pos_of_ne_zero
  intro hz
  have : iter i 0 = 0 := by
    clear hi; induction i with
    | zero => rfl
    | succ i ih => rw [iter_succ, show step 0 = 0 from rfl, ih]
  rw [← hz] at this; omega

/-- **Eine Restklasse genügt.** Die Vermutung ist äquivalent dazu, dass alle Zahlen einer
einzigen, beliebig gewählten Restklasse `s` modulo `2^k` die 1 erreichen. -/
theorem conjecture_iff_class (k s : Nat) :
    CollatzConjecture ↔ ∀ m, 0 < m → m % 2 ^ k = s % 2 ^ k → ReachesOne m := by
  constructor
  · intro h m hm _; exact h m hm
  · intro h
    apply Classical.byContradiction
    intro hc
    obtain ⟨m, hm, hs, hr⟩ := counterexample_in_every_class hc k s
    exact hr (h m hm hs)

end Collatz
