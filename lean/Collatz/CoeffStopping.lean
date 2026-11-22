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

/-! ## Nachrechnen für kleine `n` -/

theorem Titer_succ' (j n : Nat) : Titer (j + 1) n = T (Titer j n) := by
  rw [Titer_add]; rfl

/-- Läuft die Folge von `n` entlang, bis zum ersten Schritt mit `3^o < 2^j`, und prüft dort
`T^j(n) < n`. -/
def cstLoop (n : Nat) : (fuel j x P Q : Nat) → Bool
  | 0, _, _, _, _ => false
  | f + 1, j, x, P, Q =>
    if P < Q then decide (x < n)
    else cstLoop n f (j + 1) (T x) (if x % 2 = 1 then 3 * P else P) (2 * Q)

theorem cstLoop_sound (n : Nat) : ∀ f j x P Q, x = Titer j n → P = 3 ^ oddsT j n → Q = 2 ^ j →
    (∀ i, i < j → 2 ^ i ≤ 3 ^ oddsT i n) → cstLoop n f j x P Q = true →
    ∀ j', 3 ^ oddsT j' n < 2 ^ j' → (∀ i, i < j' → 2 ^ i ≤ 3 ^ oddsT i n) → Titer j' n < n := by
  intro f
  induction f with
  | zero => intro j x P Q _ _ _ _ h; simp [cstLoop] at h
  | succ f ih =>
    intro j x P Q hx hP hQ hpre h j' h3 hpre'
    unfold cstLoop at h
    by_cases hPQ : P < Q
    · rw [if_pos hPQ] at h
      have hlt : x < n := of_decide_eq_true h
      have hj : j' = j := by
        rcases Nat.lt_trichotomy j' j with hl | he | hg
        · exact absurd (hpre j' hl) (by omega)
        · exact he
        · have := hpre' j hg; subst hP hQ; omega
      subst hj; rw [← hx]; exact hlt
    · rw [if_neg hPQ] at h
      refine ih (j + 1) _ _ _ (by rw [hx, Titer_succ']) ?_ (by rw [hQ, Nat.pow_succ]; omega) ?_ h j' h3 hpre'
      · rw [oddsT_succ, hP, ← hx]
        by_cases hodd : x % 2 = 1
        · rw [if_pos hodd, if_pos hodd, Nat.pow_succ]; omega
        · rw [if_neg hodd, if_neg hodd, Nat.add_zero]
      · intro i hi
        by_cases hij : i = j
        · subst hij hP hQ; omega
        · exact hpre i (by omega)

/-- Prüft die Koeffizienten-Stoppzeit-Vermutung für alle `n < N`. -/
def cstUpTo (N fuel : Nat) : Bool :=
  (List.range N).all (fun n => n < 2 || cstLoop n fuel 0 n 1 1)

theorem cst_of_cstUpTo {N fuel : Nat} (h : cstUpTo N fuel = true) {n j : Nat} (hn : n < N)
    (h2 : 2 ≤ n) (h3 : 3 ^ oddsT j n < 2 ^ j) (hpre : ∀ i, i < j → 2 ^ i ≤ 3 ^ oddsT i n) :
    Titer j n < n := by
  unfold cstUpTo at h
  rw [List.all_eq_true] at h
  have := h n (List.mem_range.mpr hn)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h' | h'
  · omega
  · exact cstLoop_sound n fuel 0 n 1 1 rfl (by simp [oddsT]) rfl (fun i hi => by omega) h' j h3 hpre

/-- Kernel-Rechnung: die Vermutung gilt für alle `2 ≤ n < 4^7 = 16 384`. -/
theorem cst_below_4_7 : cstUpTo 16384 400 = true := by decide +kernel

/-- **Ein Gegenbeispiel zur Koeffizienten-Stoppzeit-Vermutung hätte `τ(n) ≥ 8`**: Ist `j`
der erste Schritt mit `3^o < 2^j` und `T^j(n) ≥ n`, so ist `n ≥ 4^7` und `j ≥ 8`. -/
theorem coeffStopping_counterexample {n j : Nat} (h2 : 2 ≤ n) (h3 : 3 ^ oddsT j n < 2 ^ j)
    (hpre : ∀ i, i < j → 2 ^ i ≤ 3 ^ oddsT i n) (hno : n ≤ Titer j n) :
    16384 ≤ n ∧ 8 ≤ j := by
  have hN : 16384 ≤ n := Nat.le_of_not_lt (fun hlt =>
    absurd (cst_of_cstUpTo cst_below_4_7 hlt h2 h3 hpre) (by omega))
  refine ⟨hN, Nat.le_of_not_lt (fun hj => ?_)⟩
  -- sonst wäre `n ≥ 4^7 ≥ 3^o · 2^j` und die Folge fiele bei `j`
  have hsmall : 3 ^ oddsT j n * 2 ^ j ≤ 16384 := by
    have h4 : 3 ^ oddsT j n * 2 ^ j ≤ 2 ^ j * 2 ^ j :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt h3)
    have h5 : 2 ^ j * 2 ^ j ≤ 2 ^ 7 * 2 ^ 7 :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (by omega))
        (Nat.pow_le_pow_right (by decide) (by omega))
    have : (2 : Nat) ^ 7 * 2 ^ 7 = 16384 := by decide
    omega
  have := descent_of_coeff_large h3 (by omega)
  omega

/-! ## Übertragung auf Zyklen der Collatz-Abbildung -/

/-- Die Schrittzahlen `k + o_k` von `T` treffen jede Collatz-Schrittzahl `i`, ausser direkt
nach einem ungeraden Glied. -/
theorem T_hits (x : Nat) : ∀ i, (∃ k, k + oddsT k x = i) ∨
    (∃ k, k + oddsT k x + 1 = i ∧ Titer k x % 2 = 1) := by
  intro i
  induction i with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ i ih =>
    rcases ih with ⟨k, hk⟩ | ⟨k, hk, hodd⟩
    · by_cases h : Titer k x % 2 = 1
      · exact Or.inr ⟨k, by omega, h⟩
      · refine Or.inl ⟨k + 1, ?_⟩
        rw [oddsT_succ, if_neg h]; omega
    · refine Or.inl ⟨k + 1, ?_⟩
      rw [oddsT_succ, if_pos hodd]; omega

/-- **Die Koeffizienten-Stoppzeit-Vermutung schliesst alle weiteren Zyklen der
Collatz-Abbildung aus.** -/
theorem no_collatz_cycle_of_coeffStopping (H : CoeffStoppingConjecture) {n p : Nat}
    (hp : Periodic n p) (h0 : 0 < n) (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : False := by
  obtain ⟨k0, hmin⟩ := exists_orbitMin n
  have hbig := nontrivial_cycle_ge_2_22 hp h0 hnt k0
  generalize hm : iter k0 n = m at hmin hbig
  -- `m` liegt im Zyklus
  have hper : iter p m = m := by
    rw [← hm, ← iter_add, Nat.add_comm, iter_add, hp.2]
  -- `m` ist ungerade, sonst wäre `m/2 < m`
  have hodd : m % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one m with he | ho
    · have := hmin 1
      simp only [iter, step_even he] at this
      omega
    · exact ho
  rcases T_hits m p with ⟨k, hk⟩ | ⟨k, hk, hTodd⟩
  · -- Titer k m = m: ein Zyklus von T
    have hc : Titer k m = m := by rw [Titer_eq_iter, hk, hper]
    have hk0 : 0 < k := by
      refine Nat.pos_of_ne_zero (fun h => ?_)
      subst h; simp [oddsT] at hk; exact absurd hk (by have := hp.1; omega)
    exact no_cycle_of_coeffStopping H hk0 hc
      (fun j => by rw [Titer_eq_iter]; exact hmin _) (by omega)
  · -- sonst wäre `m = 3y + 1` gerade
    have hy : iter (k + oddsT k m) m % 2 = 1 := by rw [← Titer_eq_iter]; exact hTodd
    have : iter p m = 3 * iter (k + oddsT k m) m + 1 := by
      rw [← hk, iter_add]
      simp only [iter]
      rw [step_odd hy]
    omega

end Collatz
