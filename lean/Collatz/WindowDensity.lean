import Collatz.FineGaps
import Collatz.LocalDensity

set_option linter.unusedSimpArgs false

/-!
# Satz 57: `y^0.665` Vorfahren in jedem Intervall `[y, (1 + 1/N)·y]`

Satz 54 zählt etwa `y^0.665` Vorfahren von `n` in jedem `[y, 2y)`, Satz 56 findet
einen Vorfahren in jedem `[y, (1+1/N)·y]`. Hier wird beides verbunden.

Man nimmt die Vorfahren aus einem kleineren Intervall `[y', 2y')` (Satz 54, `y' ≈ y / D`),
teilt es in `2Q` gleich lange Stücke und wählt das Stück mit den meisten Vorfahren
(Schubfachprinzip). Für dieses Stück gibt es **ein** Paar `(A, b)` (Fenster-Lemma), so dass
der Rückwärtsweg aus Satz 56 jeden seiner Vorfahren `c` nach `[y, (1+1/N)·y]` bringt.
Weil alle Wege gleich lang sind (`A + b` Schritte), ist `c = iter (A+b) x` durch `x` bestimmt:
verschiedene `c` geben verschiedene `x`.
-/

namespace Collatz

theorem two_pow_mul_mod_three {m : Nat} (h : m % 3 ≠ 0) (j : Nat) : (2 ^ j * m) % 3 ≠ 0 := by
  rw [Nat.mul_mod, two_pow_mod_three_parity]
  have hm : m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hm with hm | hm <;> rw [hm] <;>
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;> rw [hj] <;> decide

/-- Satz 54 mit dem Zusatz `3 ∤ x`. -/
theorem ancestors_in_dyadic3 {n : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) (k y : Nat)
    (hy : 2 ^ (k * 163) * (6 * n) ≤ 3 ^ (k * 50) * y) :
    ∃ L : List Nat, L.Nodup ∧ 58525359050790615 ^ k ≤ L.length ∧
      ∀ x ∈ L, y ≤ x ∧ x < 2 * y ∧ x % 3 ≠ 0 ∧ ∃ j, iter j x = n := by
  obtain ⟨c, i, hc1, hc3, hcn, hci⟩ := odd_ancestor h0 h3
  obtain ⟨q, hc, hq⟩ := cert50
  obtain ⟨L, hn, hl, hg⟩ := block (by decide) hc (Nat.le_refl 50) (Nat.le_refl 163)
    (fun t ht h3 => by rw [hq]; exact final50 t ht h3) k c hc1 hc3
  have h3pos : 0 < 3 ^ (k * 50) := Nat.pow_pos (by decide)
  have hmy : ∀ m ∈ L, m % 2 = 1 ∧ m ≤ y := by
    intro m hm
    obtain ⟨h1, _, hle, _, _⟩ := hg m hm
    refine ⟨h1, ?_⟩
    have h1' : 3 ^ (k * 50) * m ≤ 3 ^ (k * 50) * y :=
      Nat.le_trans hle (Nat.le_trans (Nat.mul_le_mul_left _ hcn) hy)
    exact Nat.le_of_mul_le_mul_left h1' h3pos
  refine ⟨L.map (liftTo y y), nodup_map_of_inj hn ?_, by rw [List.length_map]; exact hl, ?_⟩
  · intro a ha b hb hab
    obtain ⟨ja, hja⟩ := liftTo_pow y y a
    obtain ⟨jb, hjb⟩ := liftTo_pow y y b
    rw [hja, hjb] at hab
    exact odd_part_unique ja jb a b (hmy a ha).1 (hmy b hb).1 hab
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hm1, hmy'⟩ := hmy m hm
    obtain ⟨j, hj⟩ := liftTo_pow y y m
    refine ⟨liftTo_ge y y m (by omega) (by omega), liftTo_lt y y m (by omega),
      by rw [hj]; exact two_pow_mul_mod_three (hg m hm).2.1 j, ?_⟩
    obtain ⟨i', hi'⟩ := (hg m hm).2.2.2.2
    refine ⟨j + i' + i, ?_⟩
    rw [hj, iter_add, iter_add, iter_two_pow_mul, hi', hci]

/-- Schubfachprinzip: Liegen alle Werte `f x` unter `M`, dann hat eine Klasse mindestens
den `M`-ten Teil der Liste. -/
theorem pigeon (f : Nat → Nat) : ∀ M (l : List Nat), l.Nodup → (∀ x ∈ l, f x < M) →
    ∃ j, ∃ l' : List Nat, l'.Nodup ∧ (∀ x ∈ l', x ∈ l ∧ f x = j) ∧ l.length ≤ M * l'.length := by
  intro M
  induction M with
  | zero =>
    intro l _ hl
    cases l with
    | nil => exact ⟨0, [], List.nodup_nil, fun x hx => by simp at hx, by simp⟩
    | cons a t => exact absurd (hl a (by simp)) (by omega)
  | succ M ih =>
    intro l hnd hl
    -- l zerlegen in Klasse M und den Rest
    have split : ∀ l : List Nat, l.Nodup → ∃ l₁ l₂ : List Nat, l₁.Nodup ∧ l₂.Nodup ∧
        (∀ x ∈ l₁, x ∈ l ∧ f x = M) ∧ (∀ x ∈ l₂, x ∈ l ∧ f x ≠ M) ∧
        l.length = l₁.length + l₂.length := by
      intro l
      induction l with
      | nil => exact fun _ => ⟨[], [], List.nodup_nil, List.nodup_nil, fun x hx => by simp at hx,
          fun x hx => by simp at hx, rfl⟩
      | cons a t iht =>
        intro hn
        rw [List.nodup_cons] at hn
        obtain ⟨l₁, l₂, n1, n2, m1, m2, hlen⟩ := iht hn.2
        by_cases ha : f a = M
        · refine ⟨a :: l₁, l₂, List.nodup_cons.mpr ⟨fun h => hn.1 (m1 a h).1, n1⟩, n2, ?_, ?_, ?_⟩
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact ⟨by simp, ha⟩
            · exact ⟨List.mem_cons_of_mem _ (m1 x hx).1, (m1 x hx).2⟩
          · intro x hx; exact ⟨List.mem_cons_of_mem _ (m2 x hx).1, (m2 x hx).2⟩
          · simp [hlen]; omega
        · refine ⟨l₁, a :: l₂, n1, List.nodup_cons.mpr ⟨fun h => hn.1 (m2 a h).1, n2⟩, ?_, ?_, ?_⟩
          · intro x hx; exact ⟨List.mem_cons_of_mem _ (m1 x hx).1, (m1 x hx).2⟩
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact ⟨by simp, ha⟩
            · exact ⟨List.mem_cons_of_mem _ (m2 x hx).1, (m2 x hx).2⟩
          · simp [hlen]; omega
    obtain ⟨l₁, l₂, n1, n2, m1, m2, hlen⟩ := split l hnd
    by_cases hbig : l.length ≤ (M + 1) * l₁.length
    · exact ⟨M, l₁, n1, m1, hbig⟩
    · obtain ⟨j, l', n', m', hle⟩ := ih l₂ n2 (fun x hx => by
        have := hl x (m2 x hx).1; have := (m2 x hx).2; omega)
      refine ⟨j, l', n', fun x hx => ⟨(m2 x (m' x hx).1).1, (m' x hx).2⟩, ?_⟩
      -- (M+1)·|l₁| < |l| und |l₂| ≤ M·|l'|  ⇒  |l| ≤ (M+1)·|l'|
      have h1 : (M + 1) * l.length < l.length + (M + 1) * l₂.length := by
        rw [hlen, Nat.mul_add]; rw [hlen] at hbig; omega
      have h2 : (M + 1) * l₂.length ≤ (M + 1) * (M * l'.length) := Nat.mul_le_mul_left _ hle
      have h3 : M * l.length < M * ((M + 1) * l'.length) := by
        have e : (M + 1) * (M * l'.length) = M * ((M + 1) * l'.length) := by
          simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
        rw [Nat.succ_mul] at h1; omega
      rcases Nat.eq_zero_or_pos M with hM | hM
      · subst hM
        have : l₂ = [] := by
          cases l₂ with
          | nil => rfl
          | cons a t => exact absurd (by have := hl a (m2 a (by simp)).1; have := (m2 a (by simp)).2; omega) id
        subst this; simp at hlen; omega
      · exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_left h3)

/-- Aus einer injektiven Zuordnung `c ↦ x` eine Liste ohne Wiederholung. -/
theorem choose_list (R : Nat → Nat → Prop) (hinj : ∀ x c c', R x c → R x c' → c = c') :
    ∀ l : List Nat, l.Nodup → (∀ c ∈ l, ∃ x, R x c) →
      ∃ l' : List Nat, l'.Nodup ∧ l'.length = l.length ∧ ∀ x ∈ l', ∃ c ∈ l, R x c := by
  intro l
  induction l with
  | nil => intro _ _; exact ⟨[], List.nodup_nil, rfl, fun x hx => by simp at hx⟩
  | cons a t ih =>
    intro hn hR
    rw [List.nodup_cons] at hn
    obtain ⟨x, hx⟩ := hR a (by simp)
    obtain ⟨t', n', len', m'⟩ := ih hn.2 (fun c hc => hR c (List.mem_cons_of_mem _ hc))
    refine ⟨x :: t', List.nodup_cons.mpr ⟨fun h => ?_, n'⟩, by simp [len'], ?_⟩
    · obtain ⟨c, hc, hxc⟩ := m' x h
      exact hn.1 (hinj x a c hx hxc ▸ hc)
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨a, by simp, hx⟩
      · obtain ⟨c, hc, hzc⟩ := m' z hz; exact ⟨c, List.mem_cons_of_mem _ hc, hzc⟩

/-- Landen im Zielfenster: liegt `c` in `[z, (1+1/Q)·z]` und trifft `2^A·z/3^b` das Fenster,
dann liegt der Rückwärts-Vorfahre `x` von `c` in `[y, (1+1/N)·y]` (mit `Q = 8N`). -/
theorem land {N Q B A b c z y x : Nat} (hN : 1 ≤ N) (hQ : Q = 8 * N) (hB : 0 < B) (hbB : b ≤ B)
    (hzc : z ≤ c) (hcz : Q * c ≤ (Q + 1) * z)
    (hlow : y * (Q + 1) * 3 ^ b ≤ 2 ^ A * (Q * z))
    (hupp : Q * (2 ^ A * (Q * z)) ≤ (Q + 1) * (y * (Q + 1) * 3 ^ b))
    (u : 3 ^ b * x ≤ 2 ^ A * c)
    (l : 2 ^ A * c * ((Q + 1) * B) ^ b ≤ 3 ^ b * x * ((Q + 1) * B + 1) ^ b) :
    y ≤ x ∧ N * x ≤ (N + 1) * y := by
  constructor
  · have hK : (Q + 1) * b ≤ (Q + 1) * B := Nat.mul_le_mul_left _ hbB
    have hr := pow_ratio_le (F := Q) (K := (Q + 1) * B) (b := b) hK
      (Nat.mul_pos (by omega) hB)
    have hG : 0 < (Q + 1) * 3 ^ b * ((Q + 1) * B) ^ b :=
      Nat.mul_pos (Nat.mul_pos (by omega) (Nat.pow_pos (by decide)))
        (Nat.pow_pos (Nat.mul_pos (by omega) hB))
    apply Nat.le_of_mul_le_mul_right _ hG
    calc y * ((Q + 1) * 3 ^ b * ((Q + 1) * B) ^ b)
          = (y * (Q + 1) * 3 ^ b) * ((Q + 1) * B) ^ b := by simp only [Nat.mul_assoc]
      _ ≤ (2 ^ A * (Q * z)) * ((Q + 1) * B) ^ b := Nat.mul_le_mul_right _ hlow
      _ ≤ (2 ^ A * (Q * c)) * ((Q + 1) * B) ^ b :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hzc))
      _ = Q * (2 ^ A * c * ((Q + 1) * B) ^ b) := by
          simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ Q * (3 ^ b * x * ((Q + 1) * B + 1) ^ b) := Nat.mul_le_mul_left _ l
      _ = 3 ^ b * x * (Q * ((Q + 1) * B + 1) ^ b) := by
          simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ 3 ^ b * x * ((Q + 1) * ((Q + 1) * B) ^ b) := Nat.mul_le_mul_left _ hr
      _ = x * ((Q + 1) * 3 ^ b * ((Q + 1) * B) ^ b) := by
          simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  · -- Q³·x ≤ (Q+1)³·y, danach (1 + 1/Q)³ ≤ 1 + 1/N
    have h3b : 0 < 3 ^ b := Nat.pow_pos (by decide)
    have key : Q ^ 3 * x ≤ (Q + 1) ^ 3 * y := by
      apply Nat.le_of_mul_le_mul_right _ h3b
      calc Q ^ 3 * x * 3 ^ b = Q * Q * Q * (3 ^ b * x) := by
            simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_comm, Nat.mul_assoc,
              Nat.mul_left_comm]
        _ ≤ Q * Q * Q * (2 ^ A * c) := Nat.mul_le_mul_left _ u
        _ = Q * Q * 2 ^ A * (Q * c) := by simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
        _ ≤ Q * Q * 2 ^ A * ((Q + 1) * z) := Nat.mul_le_mul_left _ hcz
        _ = (Q + 1) * (Q * (2 ^ A * (Q * z))) := by
            simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
        _ ≤ (Q + 1) * ((Q + 1) * (y * (Q + 1) * 3 ^ b)) := Nat.mul_le_mul_left _ hupp
        _ = (Q + 1) ^ 3 * y * 3 ^ b := by
            simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_comm, Nat.mul_assoc,
              Nat.mul_left_comm]
    have hr := pow_ratio_le (F := N) (K := Q) (b := 3) (by omega) (by omega)
    have hQ3 : 0 < Q ^ 3 := Nat.pow_pos (by omega)
    apply Nat.le_of_mul_le_mul_right _ hQ3
    calc N * x * Q ^ 3 = N * (Q ^ 3 * x) := by simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ N * ((Q + 1) ^ 3 * y) := Nat.mul_le_mul_left _ key
      _ = N * (Q + 1) ^ 3 * y := by rw [Nat.mul_assoc]
      _ ≤ (N + 1) * Q ^ 3 * y := Nat.mul_le_mul_right _ hr
      _ = (N + 1) * y * Q ^ 3 := by simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]

/-- **Satz 57.** Ist `n > 0` und `3 ∤ n`, dann gibt es zu jedem `N ≥ 1` eine Konstante `C`, so dass
für jedes `k` jedes Intervall `[y, (1 + 1/N)·y]` mit `2^(163k)·6n·C ≤ 3^(50k)·y` mindestens
`58 525 359 050 790 615^k / C` verschiedene Vorfahren von `n` enthält. -/
theorem ancestors_in_window {n : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) (N : Nat) (hN : 1 ≤ N) :
    ∃ C, 0 < C ∧ ∀ k y, 2 ^ (k * 163) * (6 * n) * C ≤ 3 ^ (k * 50) * y →
      ∃ Lst : List Nat, Lst.Nodup ∧ 58525359050790615 ^ k ≤ C * Lst.length ∧
        ∀ x ∈ Lst, y ≤ x ∧ N * x ≤ (N + 1) * y ∧ ∃ j, iter j x = n := by
  obtain ⟨B, hB2, hW⟩ := window (8 * N) (by omega)
  obtain ⟨D, hD⟩ : ∃ D, D = 2 ^ (9 * B) * (8 * N) * 2 := ⟨_, rfl⟩
  obtain ⟨L0, hL0⟩ : ∃ L0, L0 = (8 * N + 1) * B + 1 := ⟨_, rfl⟩
  have hDpos : 0 < D := by rw [hD]; exact Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) (by omega)) (by decide)
  refine ⟨2 * D * (L0 + 16 * N), Nat.mul_pos (by omega) (by omega), ?_⟩
  intro k y hy
  have hC1 : 2 * D ≤ 2 * D * (L0 + 16 * N) := Nat.le_mul_of_pos_right _ (by omega)
  have hC2 : L0 + 16 * N ≤ 2 * D * (L0 + 16 * N) := Nat.le_mul_of_pos_left _ (by omega)
  have h3k : 0 < 3 ^ (k * 50) := Nat.pow_pos (by decide)
  have hX3 : 3 ^ (k * 50) ≤ 2 ^ (k * 163) * (6 * n) := by
    have : 3 ^ (k * 50) ≤ 2 ^ (k * 163) := by
      rw [Nat.mul_comm k 50, Nat.mul_comm k 163, Nat.pow_mul, Nat.pow_mul]
      exact Nat.pow_le_pow_left (by decide) k
    exact Nat.le_trans this (Nat.le_mul_of_pos_right _ (by omega))
  -- y ist mindestens C
  have hyC : 2 * D * (L0 + 16 * N) ≤ y := by
    apply Nat.le_of_mul_le_mul_left _ h3k
    exact Nat.le_trans (Nat.mul_le_mul_right _ hX3) hy
  -- das kleinere Intervall [Y', 2Y') mit Y' = y / D
  obtain ⟨Y', hY'⟩ : ∃ Y', Y' = y / D := ⟨_, rfl⟩
  have hd1 : Y' * D ≤ y := by rw [hY']; exact Nat.div_mul_le_self y D
  have hd2 : y < D * (Y' + 1) := by rw [hY']; exact Nat.lt_mul_div_succ y hDpos
  have hd3 : y ≤ 2 * (D * Y') := by rw [Nat.mul_succ] at hd2; omega
  have hcnt : 2 ^ (k * 163) * (6 * n) * (L0 + 16 * N) ≤ 3 ^ (k * 50) * Y' := by
    apply Nat.le_of_mul_le_mul_left (c := 2 * D) _ (by omega)
    calc 2 * D * (2 ^ (k * 163) * (6 * n) * (L0 + 16 * N))
          = 2 ^ (k * 163) * (6 * n) * (2 * D * (L0 + 16 * N)) := by
            simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ 3 ^ (k * 50) * y := hy
      _ ≤ 3 ^ (k * 50) * (2 * (D * Y')) := Nat.mul_le_mul_left _ hd3
      _ = 2 * D * (3 ^ (k * 50) * Y') := by simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  have hY'X : 2 ^ (k * 163) * (6 * n) ≤ 3 ^ (k * 50) * Y' :=
    Nat.le_trans (Nat.le_mul_of_pos_right _ (by omega)) hcnt
  have hY'L : L0 + 16 * N ≤ Y' := by
    apply Nat.le_of_mul_le_mul_left _ h3k
    exact Nat.le_trans (Nat.mul_le_mul_right _ hX3) hcnt
  obtain ⟨L1, hn1, hl1, hg1⟩ := ancestors_in_dyadic3 h0 h3 k Y' hY'X
  -- Stücke der Länge w
  obtain ⟨w, hw⟩ : ∃ w, w = Y' / (16 * N) + 1 := ⟨_, rfl⟩
  have hwpos : 0 < w := by rw [hw]; exact Nat.succ_pos _
  have hYw : Y' < 16 * N * w := by rw [hw]; exact Nat.lt_mul_div_succ Y' (by omega)
  have hf : ∀ c ∈ L1, (fun c => (c - Y') / w) c < 16 * N := by
    intro c hc
    obtain ⟨h1, h2, _, _⟩ := hg1 c hc
    show (c - Y') / w < 16 * N
    rw [Nat.div_lt_iff_lt_mul hwpos]; omega
  obtain ⟨j, l', hn', hm', hle'⟩ := pigeon (fun c => (c - Y') / w) (16 * N) L1 hn1 hf
  have hT : 0 < 58525359050790615 ^ k := Nat.pow_pos (by decide)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ ∈ l' := by
    cases l' with
    | nil => simp only [List.length_nil, Nat.mul_zero] at hle'; omega
    | cons a t => exact ⟨a, by simp⟩
  obtain ⟨z, hz⟩ : ∃ z, z = Y' + j * w := ⟨_, rfl⟩
  have hzc : ∀ c ∈ l', z ≤ c ∧ c < z + w ∧ Y' ≤ c ∧ c % 3 ≠ 0 ∧ ∃ i, iter i c = n := by
    intro c hc
    obtain ⟨hcL, hcj⟩ := hm' c hc
    obtain ⟨h1, h2, h3', h4⟩ := hg1 c hcL
    have e1 : (c - Y') / w * w ≤ c - Y' := Nat.div_mul_le_self _ _
    have e2 : c - Y' < w * ((c - Y') / w + 1) := Nat.lt_mul_div_succ _ hwpos
    have hcj' : (c - Y') / w = j := hcj
    rw [hcj'] at e1 e2
    rw [Nat.mul_succ, Nat.mul_comm w j] at e2
    exact ⟨by omega, by omega, h1, h3', h4⟩
  have hcz : ∀ c ∈ l', 8 * N * c ≤ (8 * N + 1) * z := by
    intro c hc
    obtain ⟨h1, h2, -, -, -⟩ := hzc c hc
    have e1 : 16 * N * (Y' / (16 * N)) ≤ Y' := Nat.mul_div_le Y' (16 * N)
    have e2 : 8 * N * w * 2 = 16 * N * (Y' / (16 * N)) + 16 * N := by
      rw [hw, show 8 * N * (Y' / (16 * N) + 1) * 2 = 16 * N * (Y' / (16 * N) + 1) by
        rw [show 16 * N = 8 * N * 2 by omega]
        simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm], Nat.mul_succ]
    have e3 : 8 * N * c < 8 * N * (z + w) := Nat.mul_lt_mul_of_pos_left h2 (by omega)
    rw [Nat.mul_add] at e3
    rw [Nat.add_mul (8 * N) 1 z, Nat.one_mul]
    omega
  have hz2 : z < 2 * Y' := by have := hzc c₀ hc₀; have := (hg1 c₀ (hm' c₀ hc₀).1).2.1; omega
  have hzpos : 0 < z := by omega
  have hwin : 2 ^ (9 * B) * (8 * N * z) ≤ y * (8 * N + 1) := by
    have : 2 ^ (9 * B) * (8 * N * z) ≤ Y' * D := by
      rw [hD]
      calc 2 ^ (9 * B) * (8 * N * z) ≤ 2 ^ (9 * B) * (8 * N * (2 * Y')) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_of_lt hz2))
        _ = Y' * (2 ^ (9 * B) * (8 * N) * 2) := by
            simp only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    exact Nat.le_trans this (Nat.le_trans hd1 (Nat.le_mul_of_pos_right _ (by omega)))
  obtain ⟨A, b, hb2, hbB, hAb, hlow, hupp⟩ :=
    hW (y * (8 * N + 1)) (8 * N * z) (Nat.mul_pos (by omega) hzpos) hwin
  let R : Nat → Nat → Prop := fun x c =>
    x % 2 = 1 ∧ iter (A + b) x = c ∧ y ≤ x ∧ N * x ≤ (N + 1) * y
  have hex : ∀ c ∈ l', ∃ x, R x c := by
    intro c hc
    obtain ⟨hzc1, -, hYc, hc3, -⟩ := hzc c hc
    obtain ⟨x, hxo, hi, u, l⟩ := reach (b - 2) (L := (8 * N + 1) * B + 1) (c := c) (A := A)
      (by omega) hc3 (by omega) (by omega)
    rw [show b - 2 + 2 = b by omega] at hi u l
    rw [Nat.add_sub_cancel] at l
    exact ⟨x, hxo, hi, land hN rfl (by omega) hbB hzc1 (hcz c hc) hlow hupp u l⟩
  obtain ⟨Lst, hnL, hlen, hmem⟩ := choose_list R
    (fun x c c' h1 h2 => h1.2.1 ▸ h2.2.1 ▸ rfl) l' hn' hex
  refine ⟨Lst, hnL, ?_, ?_⟩
  · rw [hlen]
    exact Nat.le_trans hl1 (Nat.le_trans hle' (Nat.mul_le_mul_right _ hC2 |> Nat.le_trans
      (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))))
  · intro x hx
    obtain ⟨c, hc, hxo, hi, hy1, hy2⟩ := hmem x hx
    obtain ⟨-, -, -, -, i, hci⟩ := hzc c hc
    exact ⟨hy1, hy2, A + b + i, by rw [iter_add, hi, hci]⟩

/-- Für `n = 1`: In jedem `[y, (1+1/N)·y]` erreichen etwa `y^0.665` Zahlen die 1. -/
theorem reaching_one_in_window (N : Nat) (hN : 1 ≤ N) :
    ∃ C, 0 < C ∧ ∀ k y, 2 ^ (k * 163) * 6 * C ≤ 3 ^ (k * 50) * y →
      ∃ Lst : List Nat, Lst.Nodup ∧ 58525359050790615 ^ k ≤ C * Lst.length ∧
        ∀ x ∈ Lst, y ≤ x ∧ N * x ≤ (N + 1) * y ∧ ReachesOne x := by
  obtain ⟨C, hC, h⟩ := ancestors_in_window (n := 1) (by decide) (by decide) N hN
  exact ⟨C, hC, fun k y hy => h k y (by simpa using hy)⟩

/-- Gäbe es ein Gegenbeispiel, dann lägen in jedem `[y, (1+1/N)·y]` (ab einer Schranke)
etwa `y^0.665` Gegenbeispiele. -/
theorem counterexamples_in_window (h : ¬ CollatzConjecture) (N : Nat) (hN : 1 ≤ N) :
    ∃ n C, 0 < n ∧ 0 < C ∧ ∀ k y, 2 ^ (k * 163) * (6 * n) * C ≤ 3 ^ (k * 50) * y →
      ∃ Lst : List Nat, Lst.Nodup ∧ 58525359050790615 ^ k ≤ C * Lst.length ∧
        ∀ x ∈ Lst, y ≤ x ∧ N * x ≤ (N + 1) * y ∧ ¬ ReachesOne x := by
  obtain ⟨n, hn, hr⟩ : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact h (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  obtain ⟨n', hn', h3', hr'⟩ := counterexample_not_three n hn hr
  obtain ⟨C, hC, hW⟩ := ancestors_in_window hn' h3' N hN
  refine ⟨n', C, hn', hC, fun k y hy => ?_⟩
  obtain ⟨Lst, h1, h2, h3⟩ := hW k y hy
  exact ⟨Lst, h1, h2, fun x hx => by
    obtain ⟨a, b, j, hj⟩ := h3 x hx
    exact ⟨a, b, fun hx' => hr' (hj ▸ reachesOne_iter hx' j)⟩⟩

end Collatz
