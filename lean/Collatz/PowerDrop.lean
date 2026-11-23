import Collatz.Density

set_option linter.unusedSimpArgs false

/-!
# Fast alle Zahlen fallen unter `2·n^(31/32)` (Korec-artige Verschärfung)

`Density.lean` zeigt: Fast alle `n` fallen irgendwann unter `n`. Hier verschärfen wir das,
ohne einen einzigen Wert auszurechnen, für **alle** Grössenordnungen gleichzeitig:

Für fast alle `n` im Bereich `2^(32w) ≤ n < 2^(32w+1)` gibt es ein `i` mit

  `(iter i n)^32 < 2 · n^31`,  also  `iter i n < 2^(1/32) · n^(31/32)`.

Die Folge fällt also nicht nur unter `n`, sondern um einen Faktor, der mit `n` wächst
(nämlich `2^w ≈ n^(1/32)`). Der Anteil der Ausnahmen ist höchstens `(3^32/2^51)^w ≈ 0.823^w`
und geht gegen 0.

Das ist eine schwächere, aber vollständig formal bewiesene Variante des Satzes von Korec (1994):
Für jedes `c > log 3 / log 4 ≈ 0.79` fällt fast jede Folge unter `n^c`. Wir erhalten `c = 31/32`.

**Ehrlich:** "fast alle" heisst Dichte 1, nicht "alle". Die Collatz-Vermutung folgt daraus nicht.
-/

namespace Collatz

/-! ## Abstieg um den Faktor `2^j` -/

/-- **Wenige ungerade Schritte ⇒ Abstieg um den Faktor `2^j`.** Ist `2^(j+1)·3^o ≤ 2^k`
(mit `o` ungeraden unter den ersten `k` Schritten von `n`) und `n ≥ 2^k`, so gilt
`2^j · T^k(n) < n`. Für `j = 0` ist das `descends_of_few_odds`. -/
theorem drop_of_few_odds {k j n : Nat} (hn : 2 ^ k ≤ n)
    (ho : 2 ^ (j + 1) * 3 ^ oddsT k n ≤ 2 ^ k) : 2 ^ j * Titer k n < n := by
  have hf := Titer_formula k n
  have hc := cT_bound k n
  have hX : 1 ≤ 3 ^ oddsT k n := Nat.pow_pos (by decide)
  generalize 3 ^ oddsT k n = X at hf hc ho hX
  generalize cT k n = c at hf hc
  generalize Titer k n = t at hf ⊢
  -- 2^k · t = X n + c  und  c + X ≤ X 2^k ≤ X n,  also  2^k · t < 2 X n.
  have h1 : X * 2 ^ k ≤ X * n := Nat.mul_le_mul_left X hn
  have h2 : 2 ^ k * t < 2 * (X * n) := by omega
  -- 2^j · 2^k · t < 2^(j+1) X n ≤ 2^k n
  have h3 : 2 ^ j * (2 ^ k * t) < 2 ^ j * (2 * (X * n)) :=
    Nat.mul_lt_mul_of_pos_left h2 (Nat.pow_pos (by decide))
  have h4 : 2 ^ (j + 1) * X * n ≤ 2 ^ k * n := Nat.mul_le_mul_right n ho
  have e1 : 2 ^ j * (2 * (X * n)) = 2 ^ (j + 1) * X * n := by
    rw [Nat.pow_succ]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have e2 : 2 ^ j * (2 ^ k * t) = 2 ^ k * (2 ^ j * t) := Nat.mul_left_comm _ _ _
  rw [e1, e2] at h3
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_lt_of_le h3 h4)

/-! ## Die Ausnahmeklassen -/

/-- Die Klassen `r < 2^(32w)`, für die das Kriterium `2^(w+1)·3^o ≤ 2^(32w)` nicht greift. -/
def badP (w : Nat) : Nat :=
  countBelow (fun r => decide (2 ^ (32 * w) < 2 ^ (w + 1) * 3 ^ oddsT (32 * w) r)) (2 ^ (32 * w))

/-- `3^20 < 2^32`. -/
theorem three_twenty_lt : 3 ^ 20 < 2 ^ 32 := by decide

/-- Ausnahmen haben viele ungerade Schritte: mindestens `19w`. -/
theorem badP_many_odds {w r : Nat} (h : 2 ^ (32 * w) < 2 ^ (w + 1) * 3 ^ oddsT (32 * w) r) :
    19 * w ≤ oddsT (32 * w) r := by
  apply Nat.le_of_not_lt
  intro hlt
  have h1 : 2 ^ (w + 1) ≤ 3 ^ (w + 1) := Nat.pow_le_pow_left (by decide) _
  have h2 : 2 ^ (w + 1) * 3 ^ oddsT (32 * w) r ≤ 3 ^ (w + 1) * 3 ^ oddsT (32 * w) r :=
    Nat.mul_le_mul_right _ h1
  rw [← Nat.pow_add] at h2
  have h3 : 3 ^ (w + 1 + oddsT (32 * w) r) ≤ 3 ^ (20 * w) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have h4 : 3 ^ (20 * w) ≤ 2 ^ (32 * w) := by
    rw [Nat.pow_mul, Nat.pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_of_lt three_twenty_lt) _
  omega

theorem badP_mul_le (w : Nat) : badP w * 2 ^ (19 * w) ≤ 3 ^ (32 * w) := by
  have hm : badP w ≤
      countBelow (fun r => decide (19 * w ≤ oddsT (32 * w) r)) (2 ^ (32 * w)) :=
    countBelow_mono (fun r h => by
      simp only [decide_eq_true_eq] at h ⊢
      exact badP_many_odds h) _
  calc badP w * 2 ^ (19 * w)
      ≤ countBelow (fun r => decide (19 * w ≤ oddsT (32 * w) r)) (2 ^ (32 * w)) * 2 ^ (19 * w) :=
        Nat.mul_le_mul_right _ hm
    _ ≤ sumBelow (fun r => 2 ^ oddsT (32 * w) r) (2 ^ (32 * w)) := count_mul_le _ _ _
    _ = 3 ^ (32 * w) := sum_two_pow_odds _

/-! ## Bernoulli-Ungleichung und Anteil → 0 -/

/-- **Bernoulli** in ganzen Zahlen: `A^w · (A + w·d) ≤ A · (A + d)^w`. -/
theorem bernoulli_gen (A d : Nat) : ∀ w, A ^ w * (A + w * d) ≤ A * (A + d) ^ w := by
  intro w
  induction w with
  | zero => simp
  | succ w ih =>
    -- A^(w+1) (A + (w+1) d) ≤ (A + d) · A^w (A + w d) ≤ (A + d) · A (A+d)^w
    have key : A ^ (w + 1) * (A + (w + 1) * d) ≤ (A + d) * (A ^ w * (A + w * d)) := by
      rw [Nat.pow_succ]
      generalize A ^ w = P
      -- P A (A + w d + d)  ≤  (A + d) P (A + w d)
      -- ⇔ A·(A + w d + d) ≤ (A + d)(A + w d) ⇔ A² + A w d + A d ≤ A² + A w d + d A + w d²
      have e1 : P * A * (A + (w + 1) * d) = P * (A * A + A * (w * d) + A * d) := by
        simp only [Nat.succ_mul, Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_assoc,
          Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have e2 : (A + d) * (P * (A + w * d)) = P * (A * A + A * (w * d) + A * d + d * (w * d)) := by
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
          Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      rw [e1, e2]
      exact Nat.mul_le_mul_left P (Nat.le_add_right _ _)
    calc A ^ (w + 1) * (A + (w + 1) * d)
        ≤ (A + d) * (A ^ w * (A + w * d)) := key
      _ ≤ (A + d) * (A * (A + d) ^ w) := Nat.mul_le_mul_left _ ih
      _ = A * (A + d) ^ (w + 1) := by rw [Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm _ (A + d)]

/-- Die Konstanten `3^32` und `2^51`. -/
theorem consts : 3 ^ 32 = 1853020188851841 ∧ 2 ^ 51 = 2251799813685248 := by decide

/-- **Der Anteil der Ausnahmen geht gegen 0.** Für jedes `M` und jedes `w ≥ 5M + 1` sind unter
den `2^(32w)` Klassen weniger als ein `M`-tel Ausnahmen. -/
theorem badP_small (M : Nat) : ∀ w, 5 * M + 1 ≤ w → M * badP w < 2 ^ (32 * w) := by
  intro w hw
  have hb := badP_mul_le w
  obtain ⟨h3, h2⟩ := consts
  have hB := bernoulli_gen 1853020188851841 398779624833407 w
  have e3 : 3 ^ (32 * w) = 1853020188851841 ^ w := by rw [Nat.pow_mul, h3]
  have e2 : 2 ^ (32 * w) * 2 ^ (19 * w) = 2251799813685248 ^ w := by
    rw [← Nat.pow_add, ← h2, ← Nat.pow_mul]; congr 1; omega
  have hA : 1 ≤ 1853020188851841 ^ w := Nat.pow_pos (by decide)
  rw [e3] at hb
  rw [show (1853020188851841 + 398779624833407 : Nat) = 2251799813685248 by rfl] at hB
  have hwd : M * 1853020188851841 < w * 398779624833407 := by omega
  generalize badP w = c at hb ⊢
  generalize 2 ^ (32 * w) = Q at e2 ⊢
  generalize 2 ^ (19 * w) = P at hb e2
  generalize 1853020188851841 ^ w = X at hb hB hA
  generalize 2251799813685248 ^ w = Y at hB e2
  generalize (398779624833407 : Nat) = d at hB hwd
  generalize (1853020188851841 : Nat) = A at hB hwd
  -- X (A + w d) ≤ A Y  und  M A < w d  ⇒  A (M X) < A Y  ⇒  M X < Y
  have h1 : X * (M * A) < X * (w * d) := Nat.mul_lt_mul_of_pos_left hwd hA
  have h4 : X * (w * d) ≤ X * (A + w * d) := Nat.mul_le_mul_left X (Nat.le_add_left _ _)
  have h5 : A * (M * X) < A * Y := by
    have e : X * (M * A) = A * (M * X) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  have hMX : M * X < Y := Nat.lt_of_mul_lt_mul_left h5
  have h6 : M * (c * P) ≤ M * X := Nat.mul_le_mul_left M hb
  apply Nat.lt_of_not_le
  intro hle
  have h7 : Q * P ≤ M * c * P := Nat.mul_le_mul_right P hle
  rw [Nat.mul_assoc] at h7
  omega

/-! ## Der Satz für die einzelnen Zahlen -/

/-- **Potenz-Abfall.** Liegt `n` in `[2^(32w), 2^(32w+1))` und ist seine Klasse
`r = n − 2^(32w)` keine Ausnahme, so erreicht die Collatz-Folge von `n` einen Wert `x` mit
`x^32 < 2·n^31`, also `x < 2^(1/32)·n^(31/32)`. -/
theorem power_drop {w r : Nat} (hr : r < 2 ^ (32 * w))
    (h : ¬ 2 ^ (32 * w) < 2 ^ (w + 1) * 3 ^ oddsT (32 * w) r) :
    ∃ i, iter i (2 ^ (32 * w) + r) ^ 32 < 2 * (2 ^ (32 * w) + r) ^ 31 := by
  have hodd : oddsT (32 * w) (2 ^ (32 * w) + r) = oddsT (32 * w) r := by
    have := oddsT_add (32 * w) r 1
    rw [Nat.mul_one, Nat.add_comm r] at this
    exact this
  have hd := drop_of_few_odds (k := 32 * w) (j := w) (n := 2 ^ (32 * w) + r)
    (Nat.le_add_right _ _) (by rw [hodd]; omega)
  refine ⟨32 * w + oddsT (32 * w) (2 ^ (32 * w) + r), ?_⟩
  rw [← Titer_eq_iter]
  generalize Titer (32 * w) (2 ^ (32 * w) + r) = x at hd ⊢
  generalize hn : 2 ^ (32 * w) + r = n at hd ⊢
  have hn2 : n < 2 * 2 ^ (32 * w) := by omega
  -- (2^w x)^32 < n^32,  2^(32w) x^32 < n^31 · n < n^31 · 2 · 2^(32w)
  have h1 : (2 ^ w * x) ^ 32 < n ^ 32 := Nat.pow_lt_pow_left hd (by decide)
  rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm w 32] at h1
  have h2 : n ^ 32 = n ^ 31 * n := Nat.pow_succ ..
  have h3 : n ^ 31 * n ≤ n ^ 31 * (2 * 2 ^ (32 * w)) := Nat.mul_le_mul_left _ (Nat.le_of_lt hn2)
  have h4 : 2 ^ (32 * w) * x ^ 32 < 2 ^ (32 * w) * (2 * n ^ 31) := by
    rw [show 2 ^ (32 * w) * (2 * n ^ 31) = n ^ 31 * (2 * 2 ^ (32 * w)) by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]]
    omega
  exact Nat.lt_of_mul_lt_mul_left h4

/-- **Zusammengefasst:** Für jedes `M` und jedes `w ≥ 5M + 1` gilt: Alle Zahlen
`n = 2^(32w) + r` (`r < 2^(32w)`) erreichen einen Wert `x` mit `x^32 < 2·n^31`, ausser höchstens
`badP w` vielen, und `M · badP w < 2^(32w)`. Der Anteil der Ausnahmen ist also kleiner als `1/M`. -/
theorem almost_all_power_drop (M w : Nat) (hw : 5 * M + 1 ≤ w) :
    M * badP w < 2 ^ (32 * w) ∧
    ∀ r, r < 2 ^ (32 * w) → ¬ 2 ^ (32 * w) < 2 ^ (w + 1) * 3 ^ oddsT (32 * w) r →
      ∃ i, iter i (2 ^ (32 * w) + r) ^ 32 < 2 * (2 ^ (32 * w) + r) ^ 31 :=
  ⟨badP_small M w hw, fun _ hr h => power_drop hr h⟩

end Collatz
