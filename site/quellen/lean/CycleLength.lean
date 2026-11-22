import Collatz.Cycles

/-!
# Ein weiterer Zyklus hätte mindestens 2510 Schritte

Wir zählen in den ersten `k` Schritten ab `n` die ungeraden (`odd`) und geraden (`even`)
Glieder. Zwei Abschätzungen gelten entlang jeder Folge:

* **unten:** `3^odd · n ≤ 2^even · x` (mit `x = iter k n`), echt kleiner sobald `odd ≥ 1`,
  weil `3x + 1 > 3x` und `2 · (x/2) = x`;
* **oben:** wenn alle Glieder `≥ m` sind: `m^odd · 2^even · x ≤ (3m+1)^odd · n`,
  weil `m · (3x + 1) ≤ (3m + 1) · x` für `x ≥ m`.

Für einen Zyklus (`x = n` nach `p` Schritten) folgt `3^j < 2^e` und `2^e · m^j ≤ (3m+1)^j`.
Mit `m = 100 001` (Cycles.lean) prüft der Kernel, dass das für `j ≤ 970` unmöglich ist.
Also hat jeder nichttriviale Zyklus mindestens 971 ungerade und 1539 gerade Glieder.
-/

namespace Collatz

/-- Anzahl ungerader Glieder unter `iter 0 n, …, iter (k-1) n`. -/
def oddCount (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => oddCount n k + (if iter k n % 2 = 1 then 1 else 0)

/-- Anzahl gerader Glieder unter `iter 0 n, …, iter (k-1) n`. -/
def evenCount (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => evenCount n k + (if iter k n % 2 = 1 then 0 else 1)

theorem odd_add_even (n : Nat) : ∀ k, oddCount n k + evenCount n k = k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp only [oddCount, evenCount]; split <;> omega

/-- **Untere Abschätzung**: `3^odd · n ≤ 2^even · iter k n`, echt sobald ein ungerader
Schritt dabei war. -/
theorem lower_bound (n : Nat) : ∀ k,
    3 ^ oddCount n k * n ≤ 2 ^ evenCount n k * iter k n ∧
    (0 < oddCount n k → 3 ^ oddCount n k * n < 2 ^ evenCount n k * iter k n) := by
  intro k
  induction k with
  | zero => simp [oddCount, evenCount]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hpos : 0 < 2 ^ evenCount n k := Nat.pow_pos (by decide)
    rw [iter_succ']
    simp only [oddCount, evenCount]
    by_cases hx : iter k n % 2 = 1
    · -- ungerader Schritt: x ↦ 3x + 1
      simp only [hx, if_true, Nat.add_zero, step_odd hx]
      have key : 3 ^ (oddCount n k + 1) * n ≤ 3 * (2 ^ evenCount n k * iter k n) := by
        rw [Nat.pow_succ, Nat.mul_comm (3 ^ oddCount n k) 3, Nat.mul_assoc]
        exact Nat.mul_le_mul_left 3 ih1
      have key2 : 3 * (2 ^ evenCount n k * iter k n) < 2 ^ evenCount n k * (3 * iter k n + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
        omega
      exact ⟨by omega, fun _ => by omega⟩
    · -- gerader Schritt: x ↦ x / 2
      have hx0 : iter k n % 2 = 0 := by omega
      simp only [hx, if_false, Nat.add_zero, step_even hx0]
      have e : 2 ^ (evenCount n k + 1) * (iter k n / 2) = 2 ^ evenCount n k * iter k n := by
        rw [Nat.pow_succ, Nat.mul_assoc]
        congr 1
        omega
      rw [e]
      exact ⟨ih1, ih2⟩

/-- **Obere Abschätzung**: Sind alle Glieder `≥ m`, so gilt
`m^odd · 2^even · iter k n ≤ (3m+1)^odd · n`. -/
theorem upper_bound (n m : Nat) : ∀ k, (∀ i, i < k → m ≤ iter i n) →
    m ^ oddCount n k * (2 ^ evenCount n k * iter k n) ≤ (3 * m + 1) ^ oddCount n k * n := by
  intro k
  induction k with
  | zero => intro _; simp [oddCount, evenCount]
  | succ k ih =>
    intro hm
    have ih' := ih (fun i hi => hm i (by omega))
    have hmk := hm k (by omega)
    rw [iter_succ']
    simp only [oddCount, evenCount]
    by_cases hx : iter k n % 2 = 1
    · simp only [hx, if_true, Nat.add_zero, step_odd hx]
      -- m (3x+1) ≤ (3m+1) x
      have hloc : m * (3 * iter k n + 1) ≤ (3 * m + 1) * iter k n := by
        rw [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_left_comm, Nat.mul_assoc]
        omega
      calc m ^ (oddCount n k + 1) * (2 ^ evenCount n k * (3 * iter k n + 1))
          = m ^ oddCount n k * 2 ^ evenCount n k * (m * (3 * iter k n + 1)) := by
            rw [Nat.pow_succ]; ac_rfl
        _ ≤ m ^ oddCount n k * 2 ^ evenCount n k * ((3 * m + 1) * iter k n) :=
            Nat.mul_le_mul_left _ hloc
        _ = (3 * m + 1) * (m ^ oddCount n k * (2 ^ evenCount n k * iter k n)) := by ac_rfl
        _ ≤ (3 * m + 1) * ((3 * m + 1) ^ oddCount n k * n) := Nat.mul_le_mul_left _ ih'
        _ = (3 * m + 1) ^ (oddCount n k + 1) * n := by rw [Nat.pow_succ]; ac_rfl
    · have hx0 : iter k n % 2 = 0 := by omega
      simp only [hx, if_false, Nat.add_zero, step_even hx0]
      have e : 2 ^ (evenCount n k + 1) * (iter k n / 2) = 2 ^ evenCount n k * iter k n := by
        rw [Nat.pow_succ, Nat.mul_assoc]
        congr 1
        omega
      rw [e]
      exact ih'

/-- Für einen Zyklus mit `j` ungeraden und `e` geraden Gliedern, alle `≥ m`:
`3^j < 2^e` und `2^e · m^j ≤ (3m+1)^j`. -/
theorem cycle_inequalities {n p m : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hm : ∀ i, m ≤ iter i n) :
    0 < oddCount n p ∧ 3 ^ oddCount n p < 2 ^ evenCount n p ∧
    2 ^ evenCount n p * m ^ oddCount n p ≤ (3 * m + 1) ^ oddCount n p := by
  obtain ⟨hp0, hpn⟩ := hp
  have hl := lower_bound n p
  have hu := upper_bound n m p (fun i _ => hm i)
  rw [hpn] at hl hu
  have hsum := odd_add_even n p
  -- Ohne ungeraden Schritt wäre 2^p · n ≤ n, unmöglich.
  have hodd : 0 < oddCount n p := by
    by_cases h : oddCount n p = 0
    · exfalso
      rw [h] at hu
      have he : evenCount n p = p := by omega
      rw [he, Nat.pow_zero, Nat.pow_zero, Nat.one_mul, Nat.one_mul] at hu
      have : 2 ≤ 2 ^ p := by
        have := Nat.pow_le_pow_right (show 2 > 0 by decide) (show 1 ≤ p by omega)
        simpa using this
      have : 2 * n ≤ 2 ^ p * n := Nat.mul_le_mul_right n this
      omega
    · omega
  refine ⟨hodd, ?_, ?_⟩
  · exact Nat.lt_of_mul_lt_mul_right (hl.2 hodd)
  · have : 2 ^ evenCount n p * m ^ oddCount n p * n ≤ (3 * m + 1) ^ oddCount n p * n := by
      calc 2 ^ evenCount n p * m ^ oddCount n p * n
          = m ^ oddCount n p * (2 ^ evenCount n p * n) := by ac_rfl
        _ ≤ _ := hu
    exact Nat.le_of_mul_le_mul_right this h0

/-- Kernel-Rechnung: Für `1 ≤ j ≤ 970` ist `(3m+1)^j < 2^e₀ · m^j` mit `m = 100 001`
und `e₀ = log₂(3^j) + 1`, der kleinsten Zahl mit `3^j < 2^e₀`. -/
def noShortCycle (m : Nat) : Nat → Bool
  | 0 => true
  | j + 1 => ((3 * m + 1) ^ (j + 1) < 2 ^ (Nat.log2 (3 ^ (j + 1)) + 1) * m ^ (j + 1)) &&
      noShortCycle m j

theorem noShortCycle_970 : noShortCycle 100001 970 = true := by decide +kernel

theorem noShortCycle_spec {m : Nat} : ∀ J j, noShortCycle m J = true → 1 ≤ j → j ≤ J →
    (3 * m + 1) ^ j < 2 ^ (Nat.log2 (3 ^ j) + 1) * m ^ j := by
  intro J
  induction J with
  | zero => intro j _ h1 h2; omega
  | succ J ih =>
    intro j h h1 h2
    simp only [noShortCycle, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hj : j = J + 1
    · subst hj; exact h.1
    · exact ih j h.2 h1 (by omega)

/-- **Jeder nichttriviale Zyklus hat mindestens 971 ungerade Glieder.** -/
theorem cycle_odd_ge {n p : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : 971 ≤ oddCount n p := by
  have hbig := nontrivial_cycle_large hp h0 hnt
  obtain ⟨hj, h3, h2⟩ := cycle_inequalities (m := 100001) hp h0 (fun i => hbig i)
  apply Nat.lt_of_not_le
  intro hle
  have hspec := noShortCycle_spec 970 (oddCount n p) noShortCycle_970 hj (by omega)
  -- 3^j < 2^e erzwingt e ≥ log₂(3^j) + 1
  have hlog : Nat.log2 (3 ^ oddCount n p) + 1 ≤ evenCount n p := by
    have hl := Nat.log2_self_le (n := 3 ^ oddCount n p)
      (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide)))
    have : 2 ^ Nat.log2 (3 ^ oddCount n p) < 2 ^ evenCount n p := Nat.lt_of_le_of_lt hl h3
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp this
  have hmono : 2 ^ (Nat.log2 (3 ^ oddCount n p) + 1) * 100001 ^ oddCount n p ≤
      2 ^ evenCount n p * 100001 ^ oddCount n p :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hlog)
  omega

set_option exponentiation.threshold 2000 in
/-- **Jeder nichttriviale Zyklus hat mindestens 2510 Schritte**
(971 ungerade und 1539 gerade Glieder). -/
theorem cycle_length_ge {n p : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : 1539 ≤ evenCount n p ∧ 2510 ≤ p := by
  have hj := cycle_odd_ge hp h0 hnt
  have hbig := nontrivial_cycle_large hp h0 hnt
  obtain ⟨_, h3, _⟩ := cycle_inequalities (m := 100001) hp h0 (fun i => hbig i)
  have hsum := odd_add_even n p
  have h971 : 3 ^ 971 ≤ 3 ^ oddCount n p := Nat.pow_le_pow_right (by decide) hj
  have hpow : 2 ^ 1538 < 3 ^ 971 := by decide +kernel
  have he : 1538 < evenCount n p := by
    have : 2 ^ 1538 < 2 ^ evenCount n p := by omega
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp this
  omega

end Collatz
