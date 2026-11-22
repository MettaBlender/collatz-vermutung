import Collatz.Reduction

/-!
# Der Satz von Terras: Paritätsvektoren

Wir benutzen die beschleunigte Abbildung `T(n) = n/2` (gerade) bzw. `(3n+1)/2` (ungerade).
Der **Paritätsvektor** der Länge `k` von `n` ist die Folge der Paritäten von
`n, T(n), …, T^(k-1)(n)`.

**Satz von Terras (1976).** Der Paritätsvektor der Länge `k` hängt nur von `n mod 2^k` ab,
und jeder der `2^k` möglichen Vektoren kommt für **genau eine** Restklasse modulo `2^k` vor.

Dazu kommt die affine Formel `T^k(2^k·a + r) = 3^o·a + T^k(r)`, wobei `o` die Anzahl der
ungeraden Schritte ist. Das ist genau der Grund, warum das Sieb funktioniert.
-/

namespace Collatz

/-- Beschleunigte Collatz-Abbildung. -/
def T (n : Nat) : Nat := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- `T` `k`-mal angewendet. -/
def Titer : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => Titer k (T n)

/-- Paritätsvektor der Länge `k` (`true` = ungerade). -/
def parVec : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, n => (n % 2 == 1) :: parVec k (T n)

/-- Anzahl der ungeraden Glieder unter den ersten `k`. -/
def oddsT : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => (if n % 2 = 1 then 1 else 0) + oddsT k (T n)

theorem parVec_length : ∀ k n, (parVec k n).length = k := by
  intro k
  induction k with
  | zero => intro n; rfl
  | succ k ih => intro n; simp [parVec, ih]

/-- Ein Schritt von `T` auf `n + 2·b`. -/
theorem T_add_two_mul (n b : Nat) :
    T (n + 2 * b) = T n + (if n % 2 = 1 then 3 * b else b) := by
  unfold T
  by_cases h : n % 2 = 0
  · have h' : (n + 2 * b) % 2 = 0 := by omega
    rw [if_pos h', if_pos h, if_neg (by omega)]; omega
  · have h' : ¬ (n + 2 * b) % 2 = 0 := by omega
    rw [if_neg h', if_neg h, if_pos (by omega)]; omega

/-- **Affine Formel**: `T^k(n + 2^k·a) = T^k(n) + 3^o·a`, und der Paritätsvektor ändert sich
nicht. -/
theorem affine (k : Nat) : ∀ n a,
    Titer k (n + 2 ^ k * a) = Titer k n + 3 ^ oddsT k n * a ∧
    parVec k (n + 2 ^ k * a) = parVec k n := by
  induction k with
  | zero => intro n a; simp [Titer, parVec, oddsT]
  | succ k ih =>
    intro n a
    have e2 : 2 ^ (k + 1) * a = 2 * (2 ^ k * a) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    have hpar : (n + 2 ^ (k + 1) * a) % 2 = n % 2 := by rw [e2]; omega
    have hT := T_add_two_mul n (2 ^ k * a)
    rw [← e2] at hT
    by_cases h : n % 2 = 1
    · rw [if_pos h] at hT
      have e3 : 3 * (2 ^ k * a) = 2 ^ k * (3 * a) := Nat.mul_left_comm _ _ _
      rw [e3] at hT
      obtain ⟨h1, h2⟩ := ih (T n) (3 * a)
      refine ⟨?_, ?_⟩
      · simp only [Titer, oddsT, if_pos h]
        rw [hT, h1, Nat.add_comm 1 (oddsT k (T n)), Nat.pow_succ, Nat.mul_assoc]
      · simp only [parVec, hpar, hT, h2]
    · rw [if_neg h] at hT
      obtain ⟨h1, h2⟩ := ih (T n) a
      refine ⟨?_, ?_⟩
      · simp only [Titer, oddsT, hT, h1, if_neg h, Nat.zero_add]
      · simp only [parVec, hpar, hT, h2]

/-- **Der Paritätsvektor hängt nur von `n mod 2^k` ab.** -/
theorem parVec_mod (k n : Nat) : parVec k n = parVec k (n % 2 ^ k) := by
  have := (affine k (n % 2 ^ k) (n / 2 ^ k)).2
  rwa [Nat.mod_add_div] at this

theorem coprime_pow_two_three (k : Nat) : Nat.Coprime (2 ^ k) 3 :=
  Nat.Coprime.pow_left k (by decide)

/-- **Verschiedene Restklassen haben verschiedene Paritätsvektoren.** -/
theorem parVec_injective (k : Nat) : ∀ n m, n < 2 ^ k → m < 2 ^ k →
    parVec k n = parVec k m → n = m := by
  induction k with
  | zero => intro n m hn hm _; simp at hn hm; omega
  | succ k ih =>
    intro n m hn hm h
    simp only [parVec, List.cons.injEq] at h
    obtain ⟨hp, ht⟩ := h
    have hK : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hpar : n % 2 = m % 2 := by
      cases hn2 : n % 2 == 1 <;> cases hm2 : m % 2 == 1 <;> simp_all <;> omega
    by_cases he : n % 2 = 0
    · -- gerade: T n = n/2 < 2^k
      have hTn : T n = n / 2 := by unfold T; rw [if_pos he]
      have hTm : T m = m / 2 := by unfold T; rw [if_pos (by omega)]
      rw [hTn, hTm] at ht
      have := ih (n / 2) (m / 2) (by omega) (by omega) ht
      omega
    · -- ungerade: T n = 3x + 2 mit n = 2x + 1
      have hTn : T n = 3 * (n / 2) + 2 := by unfold T; rw [if_neg he]; omega
      have hTm : T m = 3 * (m / 2) + 2 := by unfold T; rw [if_neg (by omega)]; omega
      rw [hTn, hTm, parVec_mod k (3 * (n / 2) + 2), parVec_mod k (3 * (m / 2) + 2)] at ht
      have hmod := ih _ _ (Nat.mod_lt _ (Nat.pow_pos (by decide)))
        (Nat.mod_lt _ (Nat.pow_pos (by decide))) ht
      -- 2^k teilt 3·(x − y), also x − y
      have key : ∀ x y, x ≤ y → y < 2 ^ k → (3 * x + 2) % 2 ^ k = (3 * y + 2) % 2 ^ k → x = y := by
        intro x y hxy hy hxy'
        have h0 := Nat.sub_mod_eq_zero_of_mod_eq hxy'.symm
        have hsub : 3 * y + 2 - (3 * x + 2) = 3 * (y - x) := by omega
        rw [hsub] at h0
        have hd : 2 ^ k ∣ 3 * (y - x) := Nat.dvd_of_mod_eq_zero h0
        have hd' := (coprime_pow_two_three k).dvd_of_dvd_mul_left hd
        have := Nat.eq_zero_of_dvd_of_lt hd' (by omega)
        omega
      by_cases hle : n / 2 ≤ m / 2
      · have := key _ _ hle (by omega) hmod; omega
      · have := key _ _ (by omega) (by omega) hmod.symm; omega

/-- Ein Inverses von 3 modulo `2^k`. -/
theorem exists_inv_three (k : Nat) : ∃ u, 3 * u % 2 ^ k = 1 % 2 ^ k := by
  have h3 : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
    induction k with
    | zero => left; rfl
    | succ k ih => rw [Nat.pow_succ]; omega
  rcases h3 with h | h
  · refine ⟨(2 * 2 ^ k + 1) / 3, ?_⟩
    have : 3 * ((2 * 2 ^ k + 1) / 3) = 2 ^ k * 2 + 1 := by omega
    rw [this, Nat.mul_add_mod]
  · refine ⟨(2 ^ k + 1) / 3, ?_⟩
    have : 3 * ((2 ^ k + 1) / 3) = 2 ^ k + 1 := by omega
    rw [this, Nat.add_mod_left]

/-- **Jeder Paritätsvektor kommt vor.** -/
theorem parVec_surjective : ∀ (v : List Bool), ∃ n, n < 2 ^ v.length ∧ parVec v.length n = v := by
  intro v
  induction v with
  | nil => exact ⟨0, by decide, rfl⟩
  | cons b w ih =>
    obtain ⟨r, hr, hv⟩ := ih
    simp only [List.length_cons]
    have hK : 2 ^ (w.length + 1) = 2 * 2 ^ w.length := by rw [Nat.pow_succ, Nat.mul_comm]
    cases b with
    | false =>
      refine ⟨2 * r, by omega, ?_⟩
      have hT : T (2 * r) = r := by unfold T; rw [if_pos (by omega)]; omega
      simp only [parVec, hT, hv]
      have : (2 * r % 2 == 1) = false := by simp
      rw [this]
    | true =>
      -- gesucht: x < 2^k mit (3x + 2) mod 2^k = r; dann n = 2x + 1
      obtain ⟨u, hu⟩ := exists_inv_three w.length
      generalize hKk : 2 ^ w.length = K at hr hu hK
      have hK0 : 0 < K := by omega
      let s := r + 2 * K - 2
      let x := u * s % K
      have hx : x < K := Nat.mod_lt _ hK0
      have h3x : (3 * x + 2) % K = r := by
        have e1 : 3 * x % K = s % K := by
          show 3 * (u * s % K) % K = s % K
          rw [Nat.mul_mod_mod, ← Nat.mul_assoc, Nat.mul_mod, hu, ← Nat.mul_mod, Nat.one_mul]
        rw [Nat.add_mod, e1, ← Nat.add_mod]
        have : s + 2 = r + K * 2 := by omega
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
      refine ⟨2 * x + 1, by omega, ?_⟩
      have hT : T (2 * x + 1) = 3 * x + 2 := by unfold T; rw [if_neg (by omega)]; omega
      simp only [parVec, hT]
      have hodd : ((2 * x + 1) % 2 == 1) = true := by simp
      rw [hodd, parVec_mod, hKk, h3x, hv]

/-- **Satz von Terras**: Jeder Paritätsvektor der Länge `k` gehört zu genau einer
Restklasse modulo `2^k`. -/
theorem terras (v : List Bool) :
    ∃ n, n < 2 ^ v.length ∧ parVec v.length n = v ∧
      ∀ m, m < 2 ^ v.length → parVec v.length m = v → m = n := by
  obtain ⟨n, hn, hv⟩ := parVec_surjective v
  exact ⟨n, hn, hv, fun m hm hmv => parVec_injective _ m n hm hn (hmv.trans hv.symm)⟩

/-! ## Verbindung zur gewöhnlichen Collatz-Folge und Abstiegskriterium -/

theorem T_eq_iter (n : Nat) : T n = iter (1 + (if n % 2 = 1 then 1 else 0)) n := by
  unfold T
  by_cases h : n % 2 = 0
  · rw [if_pos h, if_neg (by omega)]
    simp only [Nat.add_zero, iter_succ, iter_zero, step_even h]
  · rw [if_neg h, if_pos (by omega)]
    have e1 : step n = 3 * n + 1 := step_odd (by omega)
    have e2 : step (3 * n + 1) = (3 * n + 1) / 2 := step_even (by omega)
    simp only [show 1 + 1 = 2 from rfl, iter_succ, iter_zero, e1, e2]

/-- `k` Schritte von `T` sind `k + o` gewöhnliche Collatz-Schritte. -/
theorem Titer_eq_iter : ∀ k n, Titer k n = iter (k + oddsT k n) n := by
  intro k
  induction k with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    simp only [Titer, oddsT]
    rw [ih, T_eq_iter, ← iter_add]
    congr 1
    omega

/-- **Abstiegskriterium**: Hat die Klasse `r mod 2^k` weniger ungerade als nötige Schritte,
genauer `3^o < 2^k`, und gilt `T^k(r) ≤ r`, so fällt jede Zahl `n = r + 2^k·a > r` dieser
Klasse unter sich selbst. Das ist der Kern des Restklassen-Siebs. -/
theorem descends_of_parity {k r a : Nat} (h3 : 3 ^ oddsT k r < 2 ^ k) (hT : Titer k r ≤ r)
    (ha : 0 < a) : Descends (r + 2 ^ k * a) := by
  refine ⟨k + oddsT k (r + 2 ^ k * a), ?_⟩
  rw [← Titer_eq_iter, (affine k r a).1]
  have : 3 ^ oddsT k r * a < 2 ^ k * a := Nat.mul_lt_mul_of_pos_right h3 ha
  omega

/-- Beispiel: `27` hat die ersten 5 Paritäten ungerade, ungerade, gerade, ungerade, ungerade,
und ebenso jede Zahl `27 + 32·a`. -/
example : parVec 5 27 = [true, true, false, true, true] := by decide
example : parVec 5 (27 + 32 * 1000) = parVec 5 27 := by decide

end Collatz
