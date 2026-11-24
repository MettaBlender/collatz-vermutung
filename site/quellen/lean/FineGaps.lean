import Collatz.AncestorGaps
import Collatz.TwoThreeDense

set_option linter.unusedSimpArgs false

/-!
# Satz 56: Ungerade Vorfahren in jedem Intervall `[y, (1 + 1/N)·y]`

Satz 53 fand ungerade Vorfahren von `n` in jedem `[y, 4y]`. Hier wird die Lücke beliebig fein.

Idee: Von einem ungeraden Vorfahren `c` mit `3 ∤ c` geht man rückwärts zu `x = (2^E·c - 1)/3`.
Über `E` modulo 6 kann man `x % 3` frei wählen (`grow_step`). Mit `m + 2` solchen Schritten
erreicht man für **jeden** Gesamtexponenten `A ≥ 9(m+2)` einen Vorfahren `x ≈ 2^A·c/3^(m+2)`
(`reach`), denn die Parität des letzten Exponenten lässt sich über die Restklasse davor steuern.
Ist `c` gross, ist der relative Fehler klein (`step_bounds`, `pow_ratio_le`).
Satz 55 (2^a/3^b dicht über 1) liefert schliesslich zu jedem Zielintervall passende `A, b`
mit beschränktem `b` (`window`).
-/

namespace Collatz

/-- Ein Rückwärtsschritt: aus `3x + 1 = 2^E·c` (x ungerade) folgt `iter (E+1) x = c`. -/
theorem back_step {x c E : Nat} (hx : x % 2 = 1) (h : 3 * x + 1 = 2 ^ E * c) :
    iter (E + 1) x = c := by
  show iter E (step x) = c
  rw [step_odd hx, h]; exact iter_two_pow_mul E c

theorem two_pow_mod_three_parity : ∀ E, 2 ^ E % 3 = 1 + E % 2 := by
  intro E
  induction E with
  | zero => rfl
  | succ E ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]
    rcases Nat.mod_two_eq_zero_or_one E with h | h <;> rw [h] <;> omega

/-- Wachstumsschritt: zu ungeradem `c` mit `3 ∤ c` und `t ∈ {1,2}` gibt es `E ∈ [3,8]` und
einen ungeraden Vorgänger `x` mit `3x + 1 = 2^E·c` und `x % 3 = t`. -/
theorem grow_step {c t : Nat} (h3 : c % 3 ≠ 0) (ht : t = 1 ∨ t = 2) :
    ∃ E x, 3 ≤ E ∧ E ≤ 8 ∧ 3 * x + 1 = 2 ^ E * c ∧ x % 3 = t ∧ x % 2 = 1 := by
  have hr : c % 9 = 1 ∨ c % 9 = 2 ∨ c % 9 = 4 ∨ c % 9 = 5 ∨ c % 9 = 7 ∨ c % 9 = 8 := by omega
  have key : ∀ E, 3 ≤ E → E ≤ 8 → (2 ^ E * c) % 9 = 3 * t + 1 →
      ∃ E x, 3 ≤ E ∧ E ≤ 8 ∧ 3 * x + 1 = 2 ^ E * c ∧ x % 3 = t ∧ x % 2 = 1 := by
    intro E h1 h2 hm
    have he : (2 ^ E * c) % 2 = 0 := by
      obtain ⟨k, rfl⟩ : ∃ k, E = k + 1 := ⟨E - 1, by omega⟩
      rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2, ← Nat.mul_assoc, Nat.mul_mod_left]
    exact ⟨E, (2 ^ E * c - 1) / 3, h1, h2, by omega, by omega, by omega⟩
  rcases ht with rfl | rfl <;> rcases hr with hr | hr | hr | hr | hr | hr
  · exact key 8 (by decide) (by decide) (by simp only [Nat.reducePow]; omega)
  · exact key 7 (by decide) (by decide) (by simp only [Nat.reducePow]; omega)
  · exact key 6 (by decide) (by decide) (by simp only [Nat.reducePow]; omega)
  · exact key 3 (by decide) (by decide) (by simp only [Nat.reducePow]; omega)
  · exact key 4 (by decide) (by decide) (by simp only [Nat.reducePow]; omega)
  · exact key 5 (by decide) (by decide) (by simp only [Nat.reducePow]; omega)
  · exact key 4 (by decide) (by decide) (by simp only [Nat.reducePow]; omega)
  · exact key 3 (by decide) (by decide) (by simp only [Nat.reducePow]; omega)
  · exact key 8 (by decide) (by decide) (by simp only [Nat.reducePow]; omega)
  · exact key 5 (by decide) (by decide) (by simp only [Nat.reducePow]; omega)
  · exact key 6 (by decide) (by decide) (by simp only [Nat.reducePow]; omega)
  · exact key 7 (by decide) (by decide) (by simp only [Nat.reducePow]; omega)

/-- Ein Schritt verliert relativ höchstens den Faktor `(L-1)/L`. -/
theorem step_bounds {x y E L : Nat} (h : 3 * x + 1 = 2 ^ E * y) (hE : 1 ≤ E) (hL : 1 ≤ L)
    (hy : L ≤ y) : 3 * x ≤ 2 ^ E * y ∧ 2 ^ E * y * (L - 1) ≤ 3 * x * L := by
  refine ⟨by omega, ?_⟩
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have h2 : 2 * y ≤ 2 ^ E * y :=
    Nat.mul_le_mul_right _ (by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) hE; simpa using this)
  rw [← h, Nat.add_sub_cancel, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

theorem pow_ge_of {E k : Nat} (h : k ≤ E) : 2 ^ k ≤ 2 ^ E := Nat.pow_le_pow_right (by decide) h

/-- Letzter Schritt: passt die Parität von `E` zu `x₁ % 3`, gibt es den Vorgänger. -/
theorem last_step {x₁ t E : Nat} (ht : x₁ % 3 = t) (htt : t = 1 ∨ t = 2) (hE : 1 ≤ E)
    (hp : E % 2 = t - 1) : ∃ x, 3 * x + 1 = 2 ^ E * x₁ ∧ x % 2 = 1 := by
  have hm : (2 ^ E * x₁) % 3 = 1 := by
    rw [Nat.mul_mod, two_pow_mod_three_parity, ht]
    rcases htt with rfl | rfl <;> rw [hp] <;> decide
  have he : (2 ^ E * x₁) % 2 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, E = k + 1 := ⟨E - 1, by omega⟩
    rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2, ← Nat.mul_assoc, Nat.mul_mod_left]
  exact ⟨(2 ^ E * x₁ - 1) / 3, by omega, by omega⟩

theorem same_parity {c E E' : Nat} (h3 : c % 3 ≠ 0) (h : (2 ^ E * c) % 3 = 1)
    (h' : (2 ^ E' * c) % 3 = 1) : E % 2 = E' % 2 := by
  rw [Nat.mul_mod, two_pow_mod_three_parity] at h h'
  have hc : c % 3 = 1 ∨ c % 3 = 2 := by omega
  rcases hc with hc | hc <;> rw [hc] at h h' <;>
    rcases Nat.mod_two_eq_zero_or_one E with he | he <;>
    rcases Nat.mod_two_eq_zero_or_one E' with he' | he' <;> rw [he] at h <;> rw [he'] at h' <;>
    simp_all

/-- Verketten: erst ein Schritt `c ← x₁` mit Exponent `E`, dann `k` Schritte `x₁ ← x`. -/
theorem combine {x x₁ c E A' L k : Nat} (h1 : 3 * x₁ + 1 = 2 ^ E * c) (hE : 1 ≤ E) (hL : 1 ≤ L)
    (hc : L ≤ c) (u1 : 3 ^ k * x ≤ 2 ^ A' * x₁)
    (l1 : 2 ^ A' * x₁ * (L - 1) ^ k ≤ 3 ^ k * x * L ^ k) :
    3 ^ (k + 1) * x ≤ 2 ^ (E + A') * c ∧
      2 ^ (E + A') * c * (L - 1) ^ (k + 1) ≤ 3 ^ (k + 1) * x * L ^ (k + 1) := by
  obtain ⟨s1, s2⟩ := step_bounds h1 hE hL hc
  constructor
  · calc 3 ^ (k + 1) * x = 3 * (3 ^ k * x) := by rw [Nat.pow_succ]; simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ 3 * (2 ^ A' * x₁) := Nat.mul_le_mul_left _ u1
      _ = 2 ^ A' * (3 * x₁) := by simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ 2 ^ A' * (2 ^ E * c) := Nat.mul_le_mul_left _ s1
      _ = 2 ^ (E + A') * c := by rw [Nat.pow_add]; simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  · calc 2 ^ (E + A') * c * (L - 1) ^ (k + 1)
          = 2 ^ A' * (L - 1) ^ k * (2 ^ E * c * (L - 1)) := by
            rw [Nat.pow_add, Nat.pow_succ]; simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ 2 ^ A' * (L - 1) ^ k * (3 * x₁ * L) := Nat.mul_le_mul_left _ s2
      _ = 3 * L * (2 ^ A' * x₁ * (L - 1) ^ k) := by simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ 3 * L * (3 ^ k * x * L ^ k) := Nat.mul_le_mul_left _ l1
      _ = 3 ^ (k + 1) * x * L ^ (k + 1) := by
            rw [Nat.pow_succ, Nat.pow_succ]; simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]

theorem grow_ge {c E x : Nat} (hE : 3 ≤ E) (h : 3 * x + 1 = 2 ^ E * c) (hc : 1 ≤ c) :
    2 * c ≤ x := by
  have : 8 * c ≤ 2 ^ E * c := Nat.mul_le_mul_right _ (by simpa using pow_ge_of hE)
  omega

/-- Zwei Schritte: für jedes `A ≥ 18` ein ungerader Vorfahre `x` von `c` mit `9x ≈ 2^A·c`. -/
theorem reach_two {L c A : Nat} (hL : 1 ≤ L) (h3 : c % 3 ≠ 0) (hLc : L ≤ c)
    (hA : 18 ≤ A) : ∃ x, x % 2 = 1 ∧ iter (A + 2) x = c ∧ 3 ^ 2 * x ≤ 2 ^ A * c ∧
      2 ^ A * c * (L - 1) ^ 2 ≤ 3 ^ 2 * x * L ^ 2 := by
  -- erster Schritt mit passender Restklasse t, so dass A - E₁ die richtige Parität hat
  have first : ∃ t E₁ x₁, (t = 1 ∨ t = 2) ∧ 3 ≤ E₁ ∧ E₁ ≤ 8 ∧ 3 * x₁ + 1 = 2 ^ E₁ * c ∧
      x₁ % 3 = t ∧ x₁ % 2 = 1 ∧ (A - E₁) % 2 = t - 1 := by
    obtain ⟨E, x₁, h1, h2, h3', h4, h5⟩ := grow_step h3 (Or.inl rfl)
    by_cases hp : (A - E) % 2 = 0
    · exact ⟨1, E, x₁, Or.inl rfl, h1, h2, h3', h4, h5, hp⟩
    · obtain ⟨E', x₁', g1, g2, g3, g4, g5⟩ := grow_step h3 (Or.inr rfl)
      have hs := same_parity (c := c) (E := E) (E' := E') h3 (by omega) (by omega)
      exact ⟨2, E', x₁', Or.inr rfl, g1, g2, g3, g4, g5, by omega⟩
  obtain ⟨t, E₁, x₁, ht, h1, h2, h3', h4, h5, hp⟩ := first
  obtain ⟨x, hx, hxo⟩ := last_step h4 ht (show 1 ≤ A - E₁ by omega) hp
  have hx₁ : c ≤ x₁ := by have := grow_ge h1 h3' (by omega); omega
  obtain ⟨u, l⟩ := step_bounds hx (by omega) hL (Nat.le_trans hLc hx₁)
  have hc' := combine (k := 1) h3' (by omega) hL hLc (by simpa using u) (by simpa using l)
  rw [show E₁ + (A - E₁) = A by omega] at hc'
  exact ⟨x, hxo, by rw [show A + 2 = (A - E₁ + 1) + (E₁ + 1) by omega, iter_add, back_step hxo hx,
      back_step h5 h3'],
    hc'.1, hc'.2⟩

/-- `m + 2` Schritte: für jedes `A ≥ 9(m+2)` ein ungerader Vorfahre `x` mit `3^(m+2)·x ≈ 2^A·c`. -/
theorem reach (m : Nat) : ∀ {L c A : Nat}, 1 ≤ L → c % 3 ≠ 0 → L ≤ c →
    9 * (m + 2) ≤ A → ∃ x, x % 2 = 1 ∧ iter (A + (m + 2)) x = c ∧ 3 ^ (m + 2) * x ≤ 2 ^ A * c ∧
      2 ^ A * c * (L - 1) ^ (m + 2) ≤ 3 ^ (m + 2) * x * L ^ (m + 2) := by
  induction m with
  | zero => intro L c A hL h3 hLc hA; exact reach_two hL h3 hLc (by omega)
  | succ m ih =>
    intro L c A hL h3 hLc hA
    obtain ⟨E, x₁, h1, h2, h3', h4, h5⟩ := grow_step h3 (Or.inl rfl)
    have hx₁ : c ≤ x₁ := by have := grow_ge h1 h3' (by omega); omega
    obtain ⟨x, hxo, hi, u, l⟩ :=
      ih (A := A - E) hL (by omega) (Nat.le_trans hLc hx₁) (by omega)
    have hc' := combine h3' (by omega) hL hLc u l
    rw [show E + (A - E) = A by omega] at hc'
    exact ⟨x, hxo, by
      rw [show A + (m + 1 + 2) = (A - E + (m + 2)) + (E + 1) by omega, iter_add, hi,
        back_step h5 h3'], hc'.1, hc'.2⟩

/-- Bernoulli nach oben: `(K+1)^b·(K-b) ≤ K^(b+1)` für `b ≤ K`. -/
theorem pow_succ_le : ∀ b K, b ≤ K → (K + 1) ^ b * (K - b) ≤ K ^ (b + 1) := by
  intro b
  induction b with
  | zero => intro K _; simp
  | succ b ih =>
    intro K hb
    have hk : (K + 1) * (K - (b + 1)) ≤ K * (K - b) := by
      obtain ⟨D, rfl⟩ : ∃ D, K = b + 1 + D := ⟨K - (b + 1), by omega⟩
      rw [show b + 1 + D - (b + 1) = D by omega, show b + 1 + D - b = D + 1 by omega,
        Nat.mul_succ, Nat.succ_mul]
      omega
    calc (K + 1) ^ (b + 1) * (K - (b + 1)) = (K + 1) ^ b * ((K + 1) * (K - (b + 1))) := by
          rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ (K + 1) ^ b * (K * (K - b)) := Nat.mul_le_mul_left _ hk
      _ = K * ((K + 1) ^ b * (K - b)) := by simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ K * K ^ (b + 1) := Nat.mul_le_mul_left _ (ih K (by omega))
      _ = K ^ (b + 1 + 1) := by rw [Nat.pow_succ K (b + 1), Nat.mul_comm]

/-- Für `K ≥ (F+1)·b`: `F·(K+1)^b ≤ (F+1)·K^b`, d.h. `(1+1/K)^b ≤ 1 + 1/F`. -/
theorem pow_ratio_le {F K b : Nat} (hK : (F + 1) * b ≤ K) (hK0 : 0 < K) :
    F * (K + 1) ^ b ≤ (F + 1) * K ^ b := by
  have hb : b ≤ K := Nat.le_trans (Nat.le_mul_of_pos_left b (by omega)) hK
  have h1 := pow_succ_le b K hb
  have h2 : F * K ≤ (F + 1) * (K - b) := by
    rw [Nat.mul_sub, Nat.succ_mul F K]; omega
  apply Nat.le_of_mul_le_mul_right (c := K) _ hK0
  calc F * (K + 1) ^ b * K = (K + 1) ^ b * (F * K) := by simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    _ ≤ (K + 1) ^ b * ((F + 1) * (K - b)) := Nat.mul_le_mul_left _ h2
    _ = (F + 1) * ((K + 1) ^ b * (K - b)) := by simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    _ ≤ (F + 1) * K ^ (b + 1) := Nat.mul_le_mul_left _ h1
    _ = (F + 1) * K ^ b * K := by rw [Nat.pow_succ, Nat.mul_assoc]

/-- Höchste Zweierpotenz-Stufe unter `T`, mindestens ab Stufe `A`. -/
theorem exists_top {v T : Nat} (hv : 0 < v) : ∀ d A, 2 ^ A * v ≤ T → T - 2 ^ A * v ≤ d →
    ∃ A', A ≤ A' ∧ 2 ^ A' * v ≤ T ∧ T < 2 ^ (A' + 1) * v := by
  intro d
  induction d with
  | zero => intro A h1 h2; refine ⟨A, Nat.le_refl _, h1, ?_⟩
            have : 2 ^ A * v < 2 ^ (A + 1) * v :=
              Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_succ (by decide)) hv
            omega
  | succ d ih =>
    intro A h1 h2
    by_cases h : T < 2 ^ (A + 1) * v
    · exact ⟨A, Nat.le_refl _, h1, h⟩
    · have e : 2 ^ (A + 1) * v = 2 ^ A * v + 2 ^ A * v := by rw [Nat.pow_succ, Nat.mul_two, Nat.add_mul]
      have hp : 0 < 2 ^ A * v := Nat.mul_pos (Nat.two_pow_pos A) hv
      obtain ⟨A', g1, g2, g3⟩ := ih (A + 1) (by omega) (by omega)
      exact ⟨A', by omega, g2, g3⟩

theorem first_true (P : Nat → Prop) : ∀ k, P k → ∃ j, j ≤ k ∧ P j ∧ (j = 0 ∨ ¬ P (j - 1)) := by
  intro k
  induction k with
  | zero => intro h; exact ⟨0, Nat.le_refl _, h, Or.inl rfl⟩
  | succ k ih =>
    intro h
    by_cases hk : P k
    · obtain ⟨j, h1, h2, h3⟩ := ih hk; exact ⟨j, by omega, h2, h3⟩
    · exact ⟨k + 1, Nat.le_refl _, h, Or.inr hk⟩

/-- **Fenster-Lemma.** Zu `M ≥ 1` gibt es `B`, so dass jedes genügend grosse `u/v` bis auf den
Faktor `1 + 1/M` von einem `2^A/3^b` mit `2 ≤ b ≤ B`, `A ≥ 9b` getroffen wird. -/
theorem window (M : Nat) (hM : 1 ≤ M) : ∃ B, 2 ≤ B ∧ ∀ u v, 0 < v → 2 ^ (9 * B) * v ≤ u →
    ∃ A b, 2 ≤ b ∧ b ≤ B ∧ 9 * b ≤ A ∧ u * 3 ^ b ≤ 2 ^ A * v ∧
      M * (2 ^ A * v) ≤ (M + 1) * (u * 3 ^ b) := by
  obtain ⟨a, b₀, hlo, hhi⟩ := two_three_dense M hM
  have hX : 0 < 3 ^ b₀ := Nat.pow_pos (by decide)
  -- (2^a/3^b₀)^K ≥ 2 für K = 3^b₀
  have hK : 2 * 3 ^ (b₀ * 3 ^ b₀) ≤ 2 ^ (a * 3 ^ b₀) := by
    have hb := bernoulli_nat (3 ^ b₀) (3 ^ b₀)
    have h2 : 2 * (3 ^ b₀) ^ 3 ^ b₀ ≤ (3 ^ b₀ + 1) ^ 3 ^ b₀ := by
      apply Nat.le_of_mul_le_mul_left (c := 3 ^ b₀) _ hX
      calc 3 ^ b₀ * (2 * (3 ^ b₀) ^ 3 ^ b₀) = (3 ^ b₀) ^ 3 ^ b₀ * (3 ^ b₀ + 3 ^ b₀) := by
            rw [← Nat.two_mul]; simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
        _ ≤ _ := hb
    have h3 : (3 ^ b₀ + 1) ^ 3 ^ b₀ ≤ (2 ^ a) ^ 3 ^ b₀ := Nat.pow_le_pow_left hlo _
    rw [Nat.pow_mul, Nat.pow_mul]; omega
  refine ⟨2 + b₀ * 3 ^ b₀, by omega, ?_⟩
  intro u v hv huv
  obtain ⟨A₀, hA₀, htop1, htop2⟩ := exists_top (T := 9 * u) hv (9 * u) (9 * (2 + b₀ * 3 ^ b₀))
    (by omega) (by omega)
  let P : Nat → Prop := fun k => 9 * u * 3 ^ (b₀ * k) ≤ 2 ^ (A₀ + a * k) * v
  have hPK : P (3 ^ b₀) := by
    show 9 * u * 3 ^ (b₀ * 3 ^ b₀) ≤ 2 ^ (A₀ + a * 3 ^ b₀) * v
    have hpos : 0 < 3 ^ (b₀ * 3 ^ b₀) := Nat.pow_pos (by decide)
    have e : 2 ^ (A₀ + 1) * v * 3 ^ (b₀ * 3 ^ b₀) = 2 ^ A₀ * v * (2 * 3 ^ (b₀ * 3 ^ b₀)) := by
      rw [Nat.pow_succ]; simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    calc 9 * u * 3 ^ (b₀ * 3 ^ b₀) ≤ 2 ^ (A₀ + 1) * v * 3 ^ (b₀ * 3 ^ b₀) :=
          Nat.mul_le_mul_right _ (Nat.le_of_lt htop2)
      _ = 2 ^ A₀ * v * (2 * 3 ^ (b₀ * 3 ^ b₀)) := e
      _ ≤ 2 ^ A₀ * v * 2 ^ (a * 3 ^ b₀) := Nat.mul_le_mul_left _ hK
      _ = 2 ^ (A₀ + a * 3 ^ b₀) * v := by
          rw [Nat.pow_add]; simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  obtain ⟨j, hj, hPj, hj0⟩ := first_true P _ hPK
  have hP : 9 * u * 3 ^ (b₀ * j) ≤ 2 ^ (A₀ + a * j) * v := hPj
  have hbj : b₀ * j ≤ b₀ * 3 ^ b₀ := Nat.mul_le_mul_left _ hj
  rcases hj0 with rfl | hnot
  · -- j = 0: Gleichheit 9u = 2^A₀·v
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.add_zero] at hP
    have heq : 2 ^ A₀ * v = 9 * u := by omega
    refine ⟨A₀, 2, Nat.le_refl _, by omega, by omega, ?_, ?_⟩
    · rw [heq]; simp only [Nat.reducePow]; omega
    · rw [heq, show u * 3 ^ 2 = 9 * u by simp only [Nat.reducePow]; omega]
      exact Nat.mul_le_mul_right _ (Nat.le_succ M)
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; exact absurd hP hnot
      · omega⟩
    have hQ : 2 ^ (A₀ + a * i) * v < 9 * u * 3 ^ (b₀ * i) := by
      have : ¬ P i := by simpa using hnot
      exact Nat.lt_of_not_le this
    refine ⟨A₀ + a * (i + 1), 2 + b₀ * (i + 1), by omega, by omega, by omega, ?_, ?_⟩
    · calc u * 3 ^ (2 + b₀ * (i + 1)) = 9 * u * 3 ^ (b₀ * (i + 1)) := by
            rw [Nat.pow_add]; simp only [Nat.reducePow, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ _ := hP
    · have e1 : 2 ^ (A₀ + a * (i + 1)) * v = 2 ^ a * (2 ^ (A₀ + a * i) * v) := by
        rw [Nat.mul_succ, ← Nat.add_assoc, Nat.pow_add]
        simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      have e2 : u * 3 ^ (2 + b₀ * (i + 1)) = 3 ^ b₀ * (9 * u * 3 ^ (b₀ * i)) := by
        rw [Nat.mul_succ, Nat.pow_add, Nat.pow_add]
        simp only [Nat.reducePow, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      rw [e1, e2, ← Nat.mul_assoc M, ← Nat.mul_assoc (M + 1)]
      exact Nat.mul_le_mul (Nat.le_of_lt hhi) (Nat.le_of_lt hQ)

/-- Zu `n > 0` mit `3 ∤ n` gibt es beliebig grosse ungerade Vorfahren, die nicht durch 3 teilbar sind. -/
theorem big_ancestor {n : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) :
    ∀ k, ∃ c, c % 2 = 1 ∧ c % 3 ≠ 0 ∧ 2 ^ k ≤ c ∧ ∃ i, iter i c = n := by
  intro k
  induction k with
  | zero =>
    obtain ⟨c₀, hb, -⟩ := directOdd_base h0 h3
    by_cases hc : c₀ % 3 = 0
    · have hn := hb.next
      exact ⟨4 * c₀ + 1, hn.1, by omega, by simp, hn.reaches⟩
    · exact ⟨c₀, hb.1, hc, by have := hb.1; simp; omega, hb.reaches⟩
  | succ k ih =>
    obtain ⟨c, hc, hc3, hk, i, hi⟩ := ih
    obtain ⟨E, x, h1, -, hx, hx3, hxo⟩ := grow_step hc3 (Or.inl rfl)
    have := grow_ge h1 hx (Nat.le_trans (Nat.one_le_two_pow) hk)
    exact ⟨x, hxo, by omega, by rw [Nat.pow_succ]; omega,
      ⟨(E + 1) + i, by rw [iter_add, back_step hxo hx, hi]⟩⟩

/-- **Satz 56 (feine Lücken).** Ist `n > 0` und `3 ∤ n`, dann liegt für jedes `N ≥ 1` und jedes
genügend grosse `y` ein ungerader Vorfahre von `n` im Intervall `[y, (1 + 1/N)·y]`. -/
theorem fine_gaps {n : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) (N : Nat) (hN : 1 ≤ N) :
    ∃ Y, ∀ y, Y ≤ y → ∃ x, x % 2 = 1 ∧ y ≤ x ∧ N * x ≤ (N + 1) * y ∧ ∃ i, iter i x = n := by
  obtain ⟨B, hB2, hW⟩ := window (2 * N) (by omega)
  obtain ⟨c, hc, hc3, hcL, j, hj⟩ := big_ancestor h0 h3 ((4 * N + 1) * B + 1)
  have hL : (4 * N + 1) * B + 1 ≤ c := Nat.le_trans (Nat.le_of_lt Nat.lt_two_pow_self) hcL
  refine ⟨2 ^ (9 * B) * (4 * N * c), fun y hy => ?_⟩
  have hv : 0 < 4 * N * c := Nat.mul_pos (by omega) (by omega)
  have hu : 2 ^ (9 * B) * (4 * N * c) ≤ y * (4 * N + 1) :=
    Nat.le_trans hy (Nat.le_mul_of_pos_right y (by omega))
  obtain ⟨A, b, hb2, hbB, hAb, hlow, hupp⟩ := hW (y * (4 * N + 1)) (4 * N * c) hv hu
  obtain ⟨x, hxo, hi, u, l⟩ := reach (b - 2) (L := (4 * N + 1) * B + 1) (c := c) (A := A)
    (by omega) hc3 hL (by omega)
  rw [show b - 2 + 2 = b by omega] at u l
  rw [Nat.add_sub_cancel] at l
  refine ⟨x, hxo, ?_, ?_, ⟨A + (b - 2 + 2) + j, by rw [iter_add, hi, hj]⟩⟩
  · -- untere Schranke: y ≤ x
    have hK : (4 * N + 1) * b ≤ (4 * N + 1) * B := Nat.mul_le_mul_left _ hbB
    have hr := pow_ratio_le (F := 4 * N) (K := (4 * N + 1) * B) (b := b) hK
      (Nat.mul_pos (by omega) (by omega))
    have hG : 0 < (4 * N + 1) * 3 ^ b * ((4 * N + 1) * B) ^ b :=
      Nat.mul_pos (Nat.mul_pos (by omega) (Nat.pow_pos (by decide)))
        (Nat.pow_pos (Nat.mul_pos (by omega) (by omega)))
    apply Nat.le_of_mul_le_mul_right _ hG
    calc y * ((4 * N + 1) * 3 ^ b * ((4 * N + 1) * B) ^ b)
          = (y * (4 * N + 1) * 3 ^ b) * ((4 * N + 1) * B) ^ b := by
            simp only [Nat.mul_assoc]
      _ ≤ (2 ^ A * (4 * N * c)) * ((4 * N + 1) * B) ^ b := Nat.mul_le_mul_right _ hlow
      _ = 4 * N * (2 ^ A * c * ((4 * N + 1) * B) ^ b) := by
            simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ 4 * N * (3 ^ b * x * ((4 * N + 1) * B + 1) ^ b) := Nat.mul_le_mul_left _ l
      _ = 3 ^ b * x * (4 * N * ((4 * N + 1) * B + 1) ^ b) := by
            simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ 3 ^ b * x * ((4 * N + 1) * ((4 * N + 1) * B) ^ b) := Nat.mul_le_mul_left _ hr
      _ = x * ((4 * N + 1) * 3 ^ b * ((4 * N + 1) * B) ^ b) := by
            simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  · -- obere Schranke: N·x ≤ (N+1)·y
    have hq : (2 * N + 1) * (4 * N + 1) ≤ 8 * N * (N + 1) := by
      have e1 : (2 * N + 1) * (4 * N + 1) = 8 * (N * N) + 6 * N + 1 := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.mul_assoc,
          Nat.mul_left_comm N]
        omega
      have e2 : 8 * N * (N + 1) = 8 * (N * N) + 8 * N := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
      omega
    have hG : 0 < 8 * N * 3 ^ b := Nat.mul_pos (by omega) (Nat.pow_pos (by decide))
    apply Nat.le_of_mul_le_mul_right _ hG
    have e8 : 2 * N * (4 * N) = 8 * N * N := by
      rw [show (8 : Nat) = 2 * 4 from rfl]; simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    calc N * x * (8 * N * 3 ^ b) = 2 * N * (4 * N) * (3 ^ b * x) := by
          rw [e8]; simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ 2 * N * (4 * N) * (2 ^ A * c) := Nat.mul_le_mul_left _ u
      _ = 2 * N * (2 ^ A * (4 * N * c)) := by
          simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ (2 * N + 1) * (y * (4 * N + 1) * 3 ^ b) := hupp
      _ = ((2 * N + 1) * (4 * N + 1)) * (y * 3 ^ b) := by
          simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ (8 * N * (N + 1)) * (y * 3 ^ b) := Nat.mul_le_mul_right _ hq
      _ = (N + 1) * y * (8 * N * 3 ^ b) := by
          simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]

/-- Ungerade Zahlen, die die 1 erreichen, liegen in jedem `[y, (1+1/N)·y]` für grosse `y`. -/
theorem odd_reaching_one_fine (N : Nat) (hN : 1 ≤ N) :
    ∃ Y, ∀ y, Y ≤ y → ∃ x, x % 2 = 1 ∧ y ≤ x ∧ N * x ≤ (N + 1) * y ∧ ReachesOne x := by
  obtain ⟨Y, hY⟩ := fine_gaps (n := 1) (by decide) (by decide) N hN
  exact ⟨Y, fun y hy => by
    obtain ⟨x, h1, h2, h3, hr⟩ := hY y hy; exact ⟨x, h1, h2, h3, hr⟩⟩

/-- Gäbe es ein Gegenbeispiel, so lägen ungerade Gegenbeispiele in jedem `[y, (1+1/N)·y]`
für genügend grosse `y`: Gegenbeispiele hätten dann beliebig feine relative Lücken. -/
theorem counterexamples_fine_gaps (h : ¬ CollatzConjecture) (N : Nat) (hN : 1 ≤ N) :
    ∃ Y, ∀ y, Y ≤ y → ∃ x, x % 2 = 1 ∧ y ≤ x ∧ N * x ≤ (N + 1) * y ∧ ¬ ReachesOne x := by
  obtain ⟨n, hn, hr⟩ : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact h (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  obtain ⟨n', hn', h3', hr'⟩ := counterexample_not_three n hn hr
  obtain ⟨Y, hY⟩ := fine_gaps hn' h3' N hN
  refine ⟨Y, fun y hy => ?_⟩
  obtain ⟨x, h1, h2, h3, j, hj⟩ := hY y hy
  exact ⟨x, h1, h2, h3, fun hx => hr' (hj ▸ reachesOne_iter hx j)⟩

end Collatz
