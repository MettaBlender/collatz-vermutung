import Collatz.TwoAdic

/-!
# Satz 58: Schließlich periodische Paritätsfolge ⇒ Zyklus

Ist die Paritätsfolge von `n` (unter `T`) ab einer Stelle `m` periodisch mit Periode `p`,
so ist schon `T^m(n)` ein periodischer Punkt: `T^(m+p)(n) = T^m(n)`.

Beweisidee (für alle natürlichen Zahlen, ohne Rechnung): Auf jedem Block der Länge `p`
wirkt `T^p` affin, `2^p · T^p(x) = 3^o · x + c`, mit denselben `o, c` für jeden Block,
weil `o` und `c` nur vom Paritätsvektor abhängen. Für die Folge `x_j = T^(m+jp)(n)`
gilt dann `2^(pj) · (x_(j+1) − x_j) = 3^(oj) · (x_1 − x_0)`. Da `2` und `3` teilerfremd
sind, teilt `2^(pj)` die feste Zahl `x_1 − x_0` für **jedes** `j`; also ist sie `0`.

Folgerung: Eine divergente Bahn (und überhaupt jede Bahn, die in keinen Zyklus mündet)
hat eine **aperiodische** Paritätsfolge. Im 2-adischen Bild (Satz 30) heißt das: ihr
Paritätsbild ist keine rationale 2-adische Zahl der Form „schließlich periodisch“.
-/

namespace Collatz

theorem pp_Titer_add (a b n : Nat) : Titer (a + b) n = Titer b (Titer a n) := by
  induction a generalizing n with
  | zero => simp [Titer]
  | succ a ih => rw [Nat.add_right_comm]; exact ih (T n)

theorem pp_nthPar_Titer (i a n : Nat) : nthPar i (Titer a n) = nthPar (a + i) n := by
  unfold nthPar; rw [pp_Titer_add]

/-- `oddsT` und `cT` hängen nur vom Paritätsvektor ab. -/
theorem pp_coeff_of_parVec : ∀ p a b, parVec p a = parVec p b →
    oddsT p a = oddsT p b ∧ cT p a = cT p b := by
  intro p
  induction p with
  | zero => intro a b _; exact ⟨rfl, rfl⟩
  | succ p ih =>
    intro a b h
    simp only [parVec, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ho, hc⟩ := ih (T a) (T b) h2
    have hab : (a % 2 = 1 ↔ b % 2 = 1) := by
      constructor
      · intro ha; rw [ha] at h1; simp at h1; omega
      · intro hb; rw [hb] at h1; simp at h1; omega
    simp only [oddsT, cT, ho, hc]
    by_cases ha : a % 2 = 1
    · rw [if_pos ha, if_pos (hab.mp ha), if_pos ha, if_pos (hab.mp ha)]; exact ⟨rfl, rfl⟩
    · rw [if_neg ha, if_neg (fun hb => ha (hab.mpr hb)), if_neg ha,
        if_neg (fun hb => ha (hab.mpr hb))]; exact ⟨rfl, rfl⟩

/-- Ab `m` periodische Paritäten: der Paritätsvektor jedes Blocks ist derselbe. -/
theorem pp_parVec_block {n m p : Nat} (h : ∀ i, m ≤ i → nthPar (i + p) n = nthPar i n) :
    ∀ j, parVec p (Titer (m + j * p) n) = parVec p (Titer m n) := by
  intro j
  rw [parVec_eq_map, parVec_eq_map]
  apply List.map_congr_left
  intro i _
  rw [pp_nthPar_Titer, pp_nthPar_Titer]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih, Nat.succ_mul, ← Nat.add_assoc, Nat.add_right_comm (m + j * p) p i]
    exact h _ (by omega)

/-- Die Kernabschätzung: `2^(pj)·(x_(j+1) − x_j) = 3^(oj)·(x_1 − x_0)`, additiv geschrieben. -/
theorem pp_linear {x : Nat → Nat} {P Q c : Nat} (hx : ∀ j, P * x (j + 1) = Q * x j + c) :
    ∀ j, Q ^ j * x 0 + P ^ j * x (j + 1) = Q ^ j * x 1 + P ^ j * x j := by
  intro j
  induction j with
  | zero => simp only [Nat.pow_zero, Nat.one_mul, Nat.zero_add]; omega
  | succ j ih =>
    have h1 := hx (j + 1)
    have h0 := hx j
    -- Q^(j+1) x0 + P^(j+1) x(j+2) = Q·(Q^j x0) + P^j·(Q x(j+1) + c)
    have e1 : Q ^ (j + 1) * x 0 + P ^ (j + 1) * x (j + 1 + 1)
        = Q * (Q ^ j * x 0 + P ^ j * x (j + 1)) + P ^ j * c := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc (P ^ j) P, h1]
      grind
    have e2 : Q ^ (j + 1) * x 1 + P ^ (j + 1) * x (j + 1)
        = Q * (Q ^ j * x 1 + P ^ j * x j) + P ^ j * c := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc (P ^ j) P, h0]
      grind
    rw [e1, e2, ih]

/-- Teilt `2^(pj)` die Zahl `3^(oj)·d` für alle `j` (mit `p ≥ 1`), so ist `d = 0`. -/
theorem pp_zero_of_dvd {p o d : Nat} (hp : 0 < p) (h : ∀ j, 2 ^ (p * j) ∣ 3 ^ (o * j) * d) :
    d = 0 := by
  have hj := h d
  have hc : Nat.Coprime (2 ^ (p * d)) (3 ^ (o * d)) :=
    Nat.Coprime.pow_right _ (coprime_pow_two_three _)
  have hd : 2 ^ (p * d) ∣ d := hc.dvd_of_dvd_mul_left hj
  have hlt : d < 2 ^ (p * d) := by
    have := Nat.lt_two_pow_self (n := d)
    have : 2 ^ d ≤ 2 ^ (p * d) := Nat.pow_le_pow_right (by omega) (by
      have := Nat.mul_le_mul_right d hp; omega)
    omega
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · exact h0
  · have := Nat.le_of_dvd hpos hd
    omega

/-- **Satz 58**: Ist die Paritätsfolge von `n` ab der Stelle `m` periodisch mit Periode
`p ≥ 1`, so ist `T^m(n)` ein periodischer Punkt mit `T^p(T^m n) = T^m n`. -/
theorem periodic_parity_cycle {n m p : Nat} (hp : 0 < p)
    (h : ∀ i, m ≤ i → nthPar (i + p) n = nthPar i n) :
    Titer (m + p) n = Titer m n := by
  let x : Nat → Nat := fun j => Titer (m + j * p) n
  have hblock := pp_parVec_block h
  have hstep : ∀ j, 2 ^ p * x (j + 1) = 3 ^ oddsT p (x 0) * x j + cT p (x 0) := by
    intro j
    have hf := Titer_formula p (x j)
    obtain ⟨ho, hc⟩ := pp_coeff_of_parVec p (x j) (x 0) (by
      show parVec p (Titer (m + j * p) n) = parVec p (Titer (m + 0 * p) n)
      rw [hblock j, Nat.zero_mul, Nat.add_zero])
    have hx : Titer p (x j) = x (j + 1) := by
      show Titer p (Titer (m + j * p) n) = Titer (m + (j + 1) * p) n
      rw [← pp_Titer_add, Nat.succ_mul, Nat.add_assoc]
    rw [hx, ho, hc] at hf; exact hf
  have hlin := pp_linear hstep
  have h2 : ∀ j, (2 ^ p) ^ j = 2 ^ (p * j) := fun j => (Nat.pow_mul 2 p j).symm
  have h3 : ∀ j, (3 ^ oddsT p (x 0)) ^ j = 3 ^ (oddsT p (x 0) * j) :=
    fun j => (Nat.pow_mul 3 _ j).symm
  -- beide Richtungen
  have key : x 1 = x 0 := by
    rcases Nat.le_total (x 0) (x 1) with hle | hle
    · have hd : (x 1 - x 0) = 0 := by
        apply pp_zero_of_dvd (o := oddsT p (x 0)) hp
        intro j
        have e := hlin j
        rw [h2, h3] at e
        refine ⟨x (j + 1) - x j, ?_⟩
        rw [Nat.mul_sub, Nat.mul_sub]; omega
      omega
    · have hd : (x 0 - x 1) = 0 := by
        apply pp_zero_of_dvd (o := oddsT p (x 0)) hp
        intro j
        have e := hlin j
        rw [h2, h3] at e
        refine ⟨x j - x (j + 1), ?_⟩
        rw [Nat.mul_sub, Nat.mul_sub]; omega
      omega
  have : x 1 = Titer (m + p) n := by show Titer (m + 1 * p) n = _; rw [Nat.one_mul]
  have h0 : x 0 = Titer m n := by show Titer (m + 0 * p) n = _; rw [Nat.zero_mul, Nat.add_zero]
  rw [← this, ← h0]; exact key

/-- Folgerung: Bei schließlich periodischer Paritätsfolge nimmt die Bahn nur endlich viele
Werte an, nämlich höchstens die ersten `m + p`. -/
theorem periodic_parity_finite_orbit {n m p : Nat} (hp : 0 < p)
    (h : ∀ i, m ≤ i → nthPar (i + p) n = nthPar i n) :
    ∀ i, ∃ r, r < m + p ∧ Titer i n = Titer r n := by
  have hc := periodic_parity_cycle hp h
  have hper : ∀ i, m ≤ i → Titer (i + p) n = Titer i n := by
    intro i hi
    have e : i + p = (m + p) + (i - m) := by omega
    have e' : i = m + (i - m) := by omega
    rw [e, pp_Titer_add, hc, ← pp_Titer_add, ← e']
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    by_cases hi : i < m + p
    · exact ⟨i, hi, rfl⟩
    · obtain ⟨r, hr, e⟩ := ih (i - p) (by omega)
      refine ⟨r, hr, ?_⟩
      have := hper (i - p) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at this
      rw [this, e]

/-- Summe der ersten `k` Bahnwerte. -/
def ppSum (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => ppSum n k + Titer k n

/-- **Divergente Bahnen sind aperiodisch**: Ist die Bahn von `n` unbeschränkt, so ist die
Paritätsfolge von `n` nicht schließlich periodisch. -/
theorem unbounded_aperiodic {n : Nat} (hu : ∀ B, ∃ i, B < Titer i n) :
    ¬ ∃ m p, 0 < p ∧ ∀ i, m ≤ i → nthPar (i + p) n = nthPar i n := by
  rintro ⟨m, p, hp, h⟩
  have hf := periodic_parity_finite_orbit hp h
  -- Schranke: Summe der ersten m+p Werte
  let S : Nat → Nat := fun k => ppSum n k
  have hS : ∀ k r, r < k → Titer r n ≤ S k := by
    intro k
    induction k with
    | zero => intro r hr; omega
    | succ k ih =>
      intro r hr
      have e : S (k + 1) = S k + Titer k n := rfl
      rw [e]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h' | h'
      · have := ih r h'; omega
      · subst h'; omega
  obtain ⟨i, hi⟩ := hu (S (m + p))
  obtain ⟨r, hr, e⟩ := hf i
  have := hS _ r hr
  omega

/-- Beispiel: Die Paritätsfolge von `1` ist `1,0,1,0,…`, also periodisch ab `m = 0`
mit `p = 2`, und tatsächlich ist `1` ein periodischer Punkt. -/
example : Titer 2 1 = 1 := by decide

end Collatz
