import Collatz.BlockSystem
import Collatz.BlockRatio

/-!
# Satz 77: Die Produktformel eines Zyklus und die Schranke über das Minimum

Für einen Zyklus aus `k` Blöcken (Satz 75) mit Startwerten `m₀, …, m_k = m₀`, `O = Σ oᵢ`
ungeraden Schritten und Länge `L = Σ (oᵢ + eᵢ)` gilt die **Produktformel**

  `2^L · Π mᵢ < 3^O · Π (mᵢ + 1)`.

Ist `μ` eine untere Schranke aller Blockstarts (etwa das Minimum des Zyklus), so folgt

  `2^L · μ^k < 3^O · (μ + 1)^k`,

zusammen mit `3^O < 2^L` (Satz 76, Böhm–Sontacchi) also die Einschachtelung
`3^O < 2^L < 3^O · (1 + 1/μ)^k`: ein Zyklus mit grossem Minimum und wenigen Blöcken
braucht eine extrem gute Näherung `2^L ≈ 3^O`. Das ist das elementare Gerüst, auf dem die
Ausschlüsse von Steiner, Simons–de Weger und Hercher mit Baker-Schranken aufbauen.
-/

namespace Collatz

/-- Produkt `f 0 · f 1 ⋯ f (j-1)`. -/
def bprod (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | j + 1 => bprod f j * f j

/-- Summe `o 0 + ⋯ + o (j-1)`. -/
def oSum (o : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => oSum o j + o j

theorem bprod_pos (f : Nat → Nat) (j : Nat) (h : ∀ i, i < j → 0 < f i) : 0 < bprod f j := by
  induction j with
  | zero => simp [bprod]
  | succ j ih =>
    exact Nat.mul_pos (ih (fun i hi => h i (by omega))) (h j (by omega))

/-- Zyklische Verschiebung des Produkts. -/
theorem bprod_shift (m : Nat → Nat) (j : Nat) :
    bprod (fun i => m (i + 1)) j * m 0 = m j * bprod m j := by
  induction j with
  | zero => simp [bprod]
  | succ j ih =>
    show bprod (fun i => m (i + 1)) j * m (j + 1) * m 0 = m (j + 1) * (bprod m j * m j)
    rw [Nat.mul_assoc, Nat.mul_comm (m (j + 1)), ← Nat.mul_assoc, ih]
    grind

/-- Untere Schranke für ein Produkt über ein Minimum. -/
theorem bprod_min (m : Nat → Nat) (μ j : Nat) (h : ∀ i, i < j → μ ≤ m i) :
    bprod (fun i => m i + 1) j * μ ^ j ≤ bprod m j * (μ + 1) ^ j := by
  induction j with
  | zero => simp [bprod]
  | succ j ih =>
    have ih' := ih (fun i hi => h i (by omega))
    have hj : (m j + 1) * μ ≤ m j * (μ + 1) := by
      have := h j (by omega)
      rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.mul_comm]
      omega
    show bprod (fun i => m i + 1) j * (m j + 1) * μ ^ (j + 1) ≤
      bprod m j * m j * (μ + 1) ^ (j + 1)
    have e1 : bprod (fun i => m i + 1) j * (m j + 1) * μ ^ (j + 1) =
        (bprod (fun i => m i + 1) j * μ ^ j) * ((m j + 1) * μ) := by
      rw [Nat.pow_succ]; grind
    have e2 : bprod m j * m j * (μ + 1) ^ (j + 1) =
        (bprod m j * (μ + 1) ^ j) * (m j * (μ + 1)) := by
      rw [Nat.pow_succ]; grind
    rw [e1, e2]
    exact Nat.mul_le_mul ih' hj

/-- **Satz 77a.** Produktformel eines Zyklus. -/
theorem block_product (k : Nat) (m o e : Nat → Nat) (hk : 0 < k)
    (hpos : ∀ i, i < k → 0 < o i)
    (hb : ∀ i, i < k → (∀ j, j < o i → Titer j (m i) % 2 = 1) ∧
      Titer (o i) (m i) = 2 ^ e i * m (i + 1))
    (hm : m k = m 0) :
    2 ^ blockLen o e k * bprod m k < 3 ^ oSum o k * bprod (fun i => m i + 1) k := by
  -- jeder Block: 2^(o+e) · m(i+1) < 3^o · (m i + 1)
  have hblk : ∀ i, i < k → 2 ^ (o i + e i) * m (i + 1) < 3 ^ o i * (m i + 1) := by
    intro i hi
    obtain ⟨hodd, hki⟩ := hb i hi
    have := block_map (m i) (m (i + 1)) (o i) (e i) hodd hki
    have : 0 < 2 ^ o i := Nat.pow_pos (by decide)
    omega
  -- Präfix-Ungleichung
  have hpre : ∀ j, j ≤ k →
      2 ^ blockLen o e j * bprod (fun i => m (i + 1)) j ≤
        3 ^ oSum o j * bprod (fun i => m i + 1) j := by
    intro j
    induction j with
    | zero => intro _; simp [blockLen, oSum, bprod]
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := Nat.le_of_lt (hblk j (by omega))
      have e1 : 2 ^ blockLen o e (j + 1) * bprod (fun i => m (i + 1)) (j + 1) =
          (2 ^ blockLen o e j * bprod (fun i => m (i + 1)) j) * (2 ^ (o j + e j) * m (j + 1)) := by
        show 2 ^ (blockLen o e j + (o j + e j)) * (bprod (fun i => m (i + 1)) j * m (j + 1)) = _
        rw [Nat.pow_add]; grind
      have e2 : 3 ^ oSum o (j + 1) * bprod (fun i => m i + 1) (j + 1) =
          (3 ^ oSum o j * bprod (fun i => m i + 1) j) * (3 ^ o j * (m j + 1)) := by
        show 3 ^ (oSum o j + o j) * (bprod (fun i => m i + 1) j * (m j + 1)) = _
        rw [Nat.pow_add]; grind
      rw [e1, e2]
      exact Nat.mul_le_mul h1 h2
  -- strikt im letzten Block
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hstrict : 2 ^ blockLen o e (k' + 1) * bprod (fun i => m (i + 1)) (k' + 1) <
      3 ^ oSum o (k' + 1) * bprod (fun i => m i + 1) (k' + 1) := by
    have h1 := hpre k' (by omega)
    have h2 := hblk k' (by omega)
    have e1 : 2 ^ blockLen o e (k' + 1) * bprod (fun i => m (i + 1)) (k' + 1) =
        (2 ^ blockLen o e k' * bprod (fun i => m (i + 1)) k') * (2 ^ (o k' + e k') * m (k' + 1)) := by
      show 2 ^ (blockLen o e k' + (o k' + e k')) * (bprod (fun i => m (i + 1)) k' * m (k' + 1)) = _
      rw [Nat.pow_add]; grind
    have e2 : 3 ^ oSum o (k' + 1) * bprod (fun i => m i + 1) (k' + 1) =
        (3 ^ oSum o k' * bprod (fun i => m i + 1) k') * (3 ^ o k' * (m k' + 1)) := by
      show 3 ^ (oSum o k' + o k') * (bprod (fun i => m i + 1) k' * (m k' + 1)) = _
      rw [Nat.pow_add]; grind
    rw [e1, e2]
    have hp : 0 < 3 ^ oSum o k' * bprod (fun i => m i + 1) k' :=
      Nat.mul_pos (Nat.pow_pos (by decide)) (bprod_pos _ _ (fun _ _ => by omega))
    calc (2 ^ blockLen o e k' * bprod (fun i => m (i + 1)) k') * (2 ^ (o k' + e k') * m (k' + 1))
        ≤ (3 ^ oSum o k' * bprod (fun i => m i + 1) k') * (2 ^ (o k' + e k') * m (k' + 1)) :=
          Nat.mul_le_mul_right _ h1
      _ < (3 ^ oSum o k' * bprod (fun i => m i + 1) k') * (3 ^ o k' * (m k' + 1)) :=
          Nat.mul_lt_mul_of_pos_left h2 hp
  -- zyklische Verschiebung: Π m(i+1) = Π m i
  have hsh := bprod_shift m (k' + 1)
  rw [hm] at hsh
  have hm0 : 0 < m 0 := by
    have := (hb 0 (by omega)).1 0 (hpos 0 (by omega))
    simp [Titer] at this
    omega
  have heq : bprod (fun i => m (i + 1)) (k' + 1) = bprod m (k' + 1) := by
    have : bprod (fun i => m (i + 1)) (k' + 1) * m 0 = bprod m (k' + 1) * m 0 := by
      rw [hsh, Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hm0 this
  rw [heq] at hstrict
  exact hstrict

/-- **Satz 77b.** Einschachtelung über das Minimum. -/
theorem block_min_bound (k : Nat) (m o e : Nat → Nat) (μ : Nat) (hk : 0 < k)
    (hpos : ∀ i, i < k → 0 < o i)
    (hb : ∀ i, i < k → (∀ j, j < o i → Titer j (m i) % 2 = 1) ∧
      Titer (o i) (m i) = 2 ^ e i * m (i + 1))
    (hm : m k = m 0) (hμ : ∀ i, i < k → μ ≤ m i) :
    2 ^ blockLen o e k * μ ^ k < 3 ^ oSum o k * (μ + 1) ^ k := by
  have h1 := block_product k m o e hk hpos hb hm
  have h2 := bprod_min m μ k hμ
  have hP : 0 < bprod m k := bprod_pos m k (fun i hi => by
    have := (hb i hi).1 0 (hpos i hi)
    simp [Titer] at this
    omega)
  -- Strikt: wir brauchen < ; aus h1 strikt und μ^k > 0 oder μ = 0
  rcases Nat.eq_zero_or_pos μ with h0 | h0
  · subst h0
    have : (0:Nat) ^ k = 0 := Nat.zero_pow hk
    rw [this, Nat.mul_zero]
    exact Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by omega))
  · have hlt : 2 ^ blockLen o e k * μ ^ k * bprod m k <
        3 ^ oSum o k * (μ + 1) ^ k * bprod m k := by
      calc 2 ^ blockLen o e k * μ ^ k * bprod m k
          = (2 ^ blockLen o e k * bprod m k) * μ ^ k := by grind
        _ < (3 ^ oSum o k * bprod (fun i => m i + 1) k) * μ ^ k :=
            Nat.mul_lt_mul_of_pos_right h1 (Nat.pow_pos h0)
        _ = 3 ^ oSum o k * (bprod (fun i => m i + 1) k * μ ^ k) := by grind
        _ ≤ 3 ^ oSum o k * (bprod m k * (μ + 1) ^ k) := Nat.mul_le_mul_left _ h2
        _ = 3 ^ oSum o k * (μ + 1) ^ k * bprod m k := by grind
    exact Nat.lt_of_mul_lt_mul_right hlt

end Collatz
