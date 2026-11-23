import Collatz.PowerDrop

set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 2000

/-!
# Fast alle Folgen fallen unter `2^(1/5)·n^(4/5)` (Korec 1994, für den Exponenten 4/5)

Korec hat 1994 bewiesen: Für jedes `c > log 3 / log 4 ≈ 0.7925` fällt fast jede Collatz-Folge
unter `n^c`. Hier beweisen wir das für `c = 4/5 = 0.8`, also ganz nahe an Korecs Grenze, für
alle Grössenordnungen gleichzeitig.

Statt mit Gewicht `2^o` (wie in Satz 15 und 28) zählen wir mit dem Gewicht `p^o · q^(k−o)`.
Nach Terras gilt exakt `Σ_{r<2^k} p^o(r) q^(k−o(r)) = (p+q)^k` (`sum_wt`). Mit `p = 63`,
`q = 62` ist das eine Chernoff-Schranke für die Binomialverteilung, scharf genug für `c = 4/5`.

Ergebnis (`almost_all_korec`): Für `2^(1000w) ≤ n < 2^(1000w+1)` erreicht die Folge von `n`
einen Wert `x` mit `x^5 < 2·n^4`, ausser für einen Anteil `≤ ρ^w` der Klassen, `ρ ≈ 0.9685`.
-/

namespace Collatz

/-! ## Gewichtete Summe über die Restklassen -/

theorem oddsT_le : ∀ k n, oddsT k n ≤ k := by
  intro k
  induction k with
  | zero => intro n; exact Nat.le_refl 0
  | succ k ih => intro n; simp only [oddsT]; have := ih (T n); split <;> omega

/-- Das Gewicht `p^o · q^(k−o)` einer Klasse. -/
def wt (p q k r : Nat) : Nat := p ^ oddsT k r * q ^ (k - oddsT k r)

/-- Von den Hochhebungen `r`, `r + 2^k` bekommt die eine den Faktor `p`, die andere `q`. -/
theorem pair_wt (p q k r : Nat) :
    wt p q (k + 1) r + wt p q (k + 1) (r + 2 ^ k) = (p + q) * wt p q k r := by
  have ha := (affine k r 1).1
  rw [Nat.mul_one] at ha
  have ho : oddsT k (r + 2 ^ k) = oddsT k r := by
    have := oddsT_add k r 1; rwa [Nat.mul_one] at this
  have hle := oddsT_le k r
  unfold wt
  rw [oddsT_succ, oddsT_succ, ho, ha, Nat.mul_one]
  have h3 := three_pow_odd (oddsT k r)
  generalize oddsT k r = o at hle h3 ⊢
  have e1 : k + 1 - (o + 1) = k - o := by omega
  have e2 : k + 1 - o = (k - o) + 1 := by omega
  by_cases h : Titer k r % 2 = 1
  · have : ¬ (Titer k r + 3 ^ o) % 2 = 1 := by omega
    rw [if_pos h, if_neg this]
    simp only [Nat.add_zero]
    rw [e1, e2, Nat.pow_succ, Nat.pow_succ]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  · have : (Titer k r + 3 ^ o) % 2 = 1 := by omega
    rw [if_neg h, if_pos this]
    simp only [Nat.add_zero]
    rw [e1, e2, Nat.pow_succ, Nat.pow_succ]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm]

/-- **`Σ_{r<2^k} p^o(r) · q^(k−o(r)) = (p+q)^k`.** -/
theorem sum_wt (p q : Nat) : ∀ k, sumBelow (wt p q k) (2 ^ k) = (p + q) ^ k := by
  intro k
  induction k with
  | zero => simp [sumBelow, wt, oddsT]
  | succ k ih =>
    rw [Nat.pow_succ 2 k, Nat.mul_two, sumBelow_add, sumBelow_add_fun]
    rw [sumBelow_congr (g := fun r => (p + q) * wt p q k r) (2 ^ k) (fun r _ => by
      rw [Nat.add_comm (2 ^ k) r]; exact pair_wt p q k r)]
    rw [sumBelow_mul, ih, Nat.pow_succ, Nat.mul_comm]

/-- Allgemeine Markov-Ungleichung für `countBelow`. -/
theorem count_le_sum {P : Nat → Bool} {f : Nat → Nat} {c : Nat}
    (h : ∀ i, P i = true → c ≤ f i) : ∀ N, countBelow P N * c ≤ sumBelow f N := by
  intro N
  induction N with
  | zero => simp [countBelow, sumBelow]
  | succ N ih =>
    simp only [countBelow, sumBelow, Nat.add_mul]
    by_cases hp : P N = true
    · rw [if_pos hp, Nat.one_mul]; have := h N hp; omega
    · rw [if_neg hp, Nat.zero_mul]; omega

/-- Für `q ≤ p` wächst `p^o q^(k−o)` mit `o`. -/
theorem wt_mono {p q k a o : Nat} (hpq : q ≤ p) (hao : a ≤ o) (hok : o ≤ k) :
    p ^ a * q ^ (k - a) ≤ p ^ o * q ^ (k - o) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hao
  rw [show k - a = d + (k - (a + d)) by omega, Nat.pow_add, Nat.pow_add, ← Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpq d))

/-- Chernoff-artige Zählung: `#{r : o(r) ≥ a} · p^a q^(k−a) ≤ (p+q)^k`. -/
theorem count_odds_ge {p q : Nat} (hpq : q ≤ p) (k a : Nat) :
    countBelow (fun r => decide (a ≤ oddsT k r)) (2 ^ k) * (p ^ a * q ^ (k - a)) ≤ (p + q) ^ k := by
  rw [← sum_wt p q k]
  apply count_le_sum
  intro r hr
  simp only [decide_eq_true_eq] at hr
  exact wt_mono hpq hr (oddsT_le k r)

/-! ## Der Exponent 4/5 -/

/-- Die Ausnahmeklassen modulo `2^(1000w)`: das Kriterium für den Abfall um `2^(200w)` greift
nicht. -/
def badK (w : Nat) : Nat :=
  countBelow (fun r => decide (2 ^ (1000 * w) < 2 ^ (200 * w + 1) * 3 ^ oddsT (1000 * w) r))
    (2 ^ (1000 * w))

theorem three_504 : 3 ^ 504 ≤ 2 ^ 799 := by decide +kernel

/-- Ausnahmen haben mindestens `504w` ungerade unter `1000w` Schritten. -/
theorem badK_many_odds {w r : Nat}
    (h : 2 ^ (1000 * w) < 2 ^ (200 * w + 1) * 3 ^ oddsT (1000 * w) r) :
    504 * w ≤ oddsT (1000 * w) r := by
  apply Nat.le_of_not_lt
  intro hlt
  generalize oddsT (1000 * w) r = o at h hlt
  have h1 : 3 ^ (o + 1) ≤ 3 ^ (504 * w) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 3 ^ (504 * w) ≤ 2 ^ (799 * w) := by
    rw [Nat.pow_mul, Nat.pow_mul]; exact Nat.pow_le_pow_left three_504 _
  have h3 : 2 ^ (200 * w + 1) * 2 ^ (799 * w) ≤ 2 ^ (1000 * w) := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have h4 : 2 ^ (200 * w + 1) * 3 ^ (o + 1) ≤ 2 ^ (200 * w + 1) * 2 ^ (799 * w) :=
    Nat.mul_le_mul_left _ (Nat.le_trans h1 h2)
  have e : 2 ^ (200 * w + 1) * 3 ^ (o + 1) = 3 * (2 ^ (200 * w + 1) * 3 ^ o) := by
    rw [Nat.pow_succ 3 o]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [e] at h4
  omega

theorem badK_mul_le (w : Nat) :
    badK w * ((63 ^ 504 * 62 ^ 496) ^ w) ≤ (125 ^ 1000) ^ w := by
  have hm : badK w ≤ countBelow (fun r => decide (504 * w ≤ oddsT (1000 * w) r)) (2 ^ (1000 * w)) :=
    countBelow_mono (fun r h => by
      simp only [decide_eq_true_eq] at h ⊢
      exact badK_many_odds h) _
  have hc := count_odds_ge (p := 63) (q := 62) (by decide) (1000 * w) (504 * w)
  rw [show 1000 * w - 504 * w = 496 * w by omega, show (63 + 62 : Nat) = 125 from rfl] at hc
  have e1 : 63 ^ (504 * w) * 62 ^ (496 * w) = (63 ^ 504 * 62 ^ 496) ^ w := by
    rw [Nat.mul_pow, Nat.pow_mul, Nat.pow_mul]
  have e2 : 125 ^ (1000 * w) = (125 ^ 1000) ^ w := Nat.pow_mul _ _ _
  rw [e1, e2] at hc
  exact Nat.le_trans (Nat.mul_le_mul_right _ hm) hc

/-- Die Konstanten: `A = 125^1000 < B = 2^1000 · 63^504 · 62^496` und `A ≤ 31 (B − A)`. -/
theorem korec_lt : 125 ^ 1000 < 2 ^ 1000 * (63 ^ 504 * 62 ^ 496) := by decide +kernel
theorem korec_31 : 125 ^ 1000 ≤ 31 * (2 ^ 1000 * (63 ^ 504 * 62 ^ 496) - 125 ^ 1000) := by
  decide +kernel
theorem korec_consts :
    125 ^ 1000 < 2 ^ 1000 * (63 ^ 504 * 62 ^ 496) ∧
    125 ^ 1000 ≤ 31 * (2 ^ 1000 * (63 ^ 504 * 62 ^ 496) - 125 ^ 1000) := ⟨korec_lt, korec_31⟩

/-- **Der Anteil der Ausnahmen geht gegen 0.** Für jedes `M` und `w ≥ 31M + 1`. -/
theorem badK_small (M : Nat) : ∀ w, 31 * M + 1 ≤ w → M * badK w < 2 ^ (1000 * w) := by
  intro w hw
  have hb := badK_mul_le w
  obtain ⟨hlt, h31⟩ := korec_consts
  generalize hA : (125 ^ 1000 : Nat) = A at hlt h31 hb
  generalize hG : (63 ^ 504 * 62 ^ 496 : Nat) = G at hlt h31 hb
  generalize hd : 2 ^ 1000 * G - A = d at h31
  have hB : 2 ^ 1000 * G = A + d := by omega
  have hbern := bernoulli_gen A d w
  rw [← hB, Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm 1000 w] at hbern
  rw [Nat.mul_comm w 1000] at hbern
  have hApos : 1 ≤ A ^ w := Nat.pow_pos (by rw [← hA]; exact Nat.pow_pos (by decide))
  have hGpos : 0 < G ^ w := Nat.pow_pos (by rw [← hG]; decide)
  have hwd : M * A < w * d := by
    have : M * A ≤ M * (31 * d) := Nat.mul_le_mul_left M h31
    have : (31 * M + 1) * d ≤ w * d := Nat.mul_le_mul_right d hw
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · rw [h] at h31; rw [← hA] at h31; simp at h31
      · exact h
    rw [Nat.add_mul, Nat.one_mul] at this
    have e : M * (31 * d) = 31 * M * d := by rw [← Nat.mul_assoc, Nat.mul_comm M 31]
    omega
  generalize A ^ w = X at hb hbern hApos
  generalize G ^ w = Y at hb hbern hGpos
  generalize 2 ^ (1000 * w) = Q at hbern ⊢
  generalize badK w = c at hb ⊢
  -- X (A + w d) ≤ A (Q Y),  M A < w d  ⇒  M X < Q Y;  c Y ≤ X
  have h1 : X * (M * A) < X * (w * d) := Nat.mul_lt_mul_of_pos_left hwd hApos
  have h2 : X * (w * d) ≤ X * (A + w * d) := Nat.mul_le_mul_left X (Nat.le_add_left _ _)
  have h3 : A * (M * X) < A * (Q * Y) := by
    have e : X * (M * A) = A * (M * X) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  have hMX : M * X < Q * Y := Nat.lt_of_mul_lt_mul_left h3
  have h4 : M * (c * Y) ≤ M * X := Nat.mul_le_mul_left M hb
  apply Nat.lt_of_not_le
  intro hle
  have h5 : Q * Y ≤ M * c * Y := Nat.mul_le_mul_right Y hle
  rw [Nat.mul_assoc] at h5
  omega

/-- **Abfall auf `n^(4/5)`.** Ist die Klasse `r` von `n = 2^(1000w) + r` keine Ausnahme, so
erreicht die Folge von `n` einen Wert `x` mit `x^5 < 2·n^4`. -/
theorem korec_drop {w r : Nat} (hr : r < 2 ^ (1000 * w))
    (h : ¬ 2 ^ (1000 * w) < 2 ^ (200 * w + 1) * 3 ^ oddsT (1000 * w) r) :
    ∃ i, iter i (2 ^ (1000 * w) + r) ^ 5 < 2 * (2 ^ (1000 * w) + r) ^ 4 := by
  have hodd : oddsT (1000 * w) (2 ^ (1000 * w) + r) = oddsT (1000 * w) r := by
    have := oddsT_add (1000 * w) r 1
    rw [Nat.mul_one, Nat.add_comm r] at this
    exact this
  have hd := drop_of_few_odds (k := 1000 * w) (j := 200 * w) (n := 2 ^ (1000 * w) + r)
    (Nat.le_add_right _ _) (by rw [hodd]; omega)
  refine ⟨1000 * w + oddsT (1000 * w) (2 ^ (1000 * w) + r), ?_⟩
  rw [← Titer_eq_iter]
  generalize Titer (1000 * w) (2 ^ (1000 * w) + r) = x at hd ⊢
  generalize hn : 2 ^ (1000 * w) + r = n at hd ⊢
  have hn2 : n < 2 * 2 ^ (1000 * w) := by omega
  have h1 : (2 ^ (200 * w) * x) ^ 5 < n ^ 5 := Nat.pow_lt_pow_left hd (by decide)
  rw [Nat.mul_pow, ← Nat.pow_mul, show 200 * w * 5 = 1000 * w by omega] at h1
  have h2 : n ^ 5 = n ^ 4 * n := Nat.pow_succ ..
  have h3 : n ^ 4 * n ≤ n ^ 4 * (2 * 2 ^ (1000 * w)) := Nat.mul_le_mul_left _ (Nat.le_of_lt hn2)
  have h4 : 2 ^ (1000 * w) * x ^ 5 < 2 ^ (1000 * w) * (2 * n ^ 4) := by
    rw [show 2 ^ (1000 * w) * (2 * n ^ 4) = n ^ 4 * (2 * 2 ^ (1000 * w)) by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]]
    omega
  exact Nat.lt_of_mul_lt_mul_left h4

/-- **Korec für den Exponenten 4/5.** Für jedes `M` und `w ≥ 31M + 1`: Weniger als ein `M`-tel
der Zahlen `n = 2^(1000w) + r` sind Ausnahmen, alle anderen erreichen ein `x` mit
`x^5 < 2·n^4`. -/
theorem almost_all_korec (M w : Nat) (hw : 31 * M + 1 ≤ w) :
    M * badK w < 2 ^ (1000 * w) ∧
    ∀ r, r < 2 ^ (1000 * w) → ¬ 2 ^ (1000 * w) < 2 ^ (200 * w + 1) * 3 ^ oddsT (1000 * w) r →
      ∃ i, iter i (2 ^ (1000 * w) + r) ^ 5 < 2 * (2 ^ (1000 * w) + r) ^ 4 :=
  ⟨badK_small M w hw, fun _ hr h => korec_drop hr h⟩

end Collatz
