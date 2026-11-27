import Collatz.BlockProduct

/-!
# Satz 78: Obere Schranke für das Minimum eines Zyklus

Für einen Zyklus aus `k` Blöcken (Satz 75) mit `O` ungeraden Schritten und Länge `L` gilt

* `3^O < 2^L`, also `3^O + 1 ≤ 2^L` (im Blockbild bewiesen, vgl. Böhm–Sontacchi);
* mit Satz 77 für jede untere Schranke `μ` aller Blockstarts:
  `(3^O + 1) · μ^k < 3^O · (μ + 1)^k`.

Für einen Zyklus aus **einem** Block (Steiner-Form) folgt `m < 3^o`: das ist schärfer als die
Steiner-Schranke `m < 2^(o+e)` aus Satz 73, denn `3^o < 2^(o+e)`.
-/

namespace Collatz

/-- **Satz 78a.** Wachstum im Blockbild: `3^O < 2^L`. -/
theorem block_growth (k : Nat) (m o e : Nat → Nat) (hk : 0 < k)
    (hpos : ∀ i, i < k → 0 < o i)
    (hb : ∀ i, i < k → (∀ j, j < o i → Titer j (m i) % 2 = 1) ∧
      Titer (o i) (m i) = 2 ^ e i * m (i + 1))
    (hm : m k = m 0) :
    3 ^ oSum o k < 2 ^ blockLen o e k := by
  have hblk : ∀ i, i < k → 3 ^ o i * m i < 2 ^ (o i + e i) * m (i + 1) := by
    intro i hi
    obtain ⟨hodd, hki⟩ := hb i hi
    exact (block_ratio (m i) (m (i + 1)) (o i) (e i) (hpos i hi) hodd hki).1
  have hmpos : ∀ i, i < k → 0 < m i := by
    intro i hi
    have := (hb i hi).1 0 (hpos i hi)
    simp [Titer] at this
    omega
  have hpre : ∀ j, j ≤ k →
      3 ^ oSum o j * bprod m j ≤ 2 ^ blockLen o e j * bprod (fun i => m (i + 1)) j := by
    intro j
    induction j with
    | zero => intro _; simp [blockLen, oSum, bprod]
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := Nat.le_of_lt (hblk j (by omega))
      have e1 : 3 ^ oSum o (j + 1) * bprod m (j + 1) =
          (3 ^ oSum o j * bprod m j) * (3 ^ o j * m j) := by
        show 3 ^ (oSum o j + o j) * (bprod m j * m j) = _
        rw [Nat.pow_add]; grind
      have e2 : 2 ^ blockLen o e (j + 1) * bprod (fun i => m (i + 1)) (j + 1) =
          (2 ^ blockLen o e j * bprod (fun i => m (i + 1)) j) * (2 ^ (o j + e j) * m (j + 1)) := by
        show 2 ^ (blockLen o e j + (o j + e j)) * (bprod (fun i => m (i + 1)) j * m (j + 1)) = _
        rw [Nat.pow_add]; grind
      rw [e1, e2]
      exact Nat.mul_le_mul h1 h2
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hstrict : 3 ^ oSum o (k' + 1) * bprod m (k' + 1) <
      2 ^ blockLen o e (k' + 1) * bprod (fun i => m (i + 1)) (k' + 1) := by
    have h1 := hpre k' (by omega)
    have h2 := hblk k' (by omega)
    have e1 : 3 ^ oSum o (k' + 1) * bprod m (k' + 1) =
        (3 ^ oSum o k' * bprod m k') * (3 ^ o k' * m k') := by
      show 3 ^ (oSum o k' + o k') * (bprod m k' * m k') = _
      rw [Nat.pow_add]; grind
    have e2 : 2 ^ blockLen o e (k' + 1) * bprod (fun i => m (i + 1)) (k' + 1) =
        (2 ^ blockLen o e k' * bprod (fun i => m (i + 1)) k') * (2 ^ (o k' + e k') * m (k' + 1)) := by
      show 2 ^ (blockLen o e k' + (o k' + e k')) * (bprod (fun i => m (i + 1)) k' * m (k' + 1)) = _
      rw [Nat.pow_add]; grind
    rw [e1, e2]
    have hp : 0 < 2 ^ blockLen o e k' * bprod (fun i => m (i + 1)) k' :=
      Nat.mul_pos (Nat.pow_pos (by decide)) (bprod_pos _ _ (fun i hi => by
        rcases Nat.lt_or_ge (i + 1) (k' + 1) with h | h
        · exact hmpos (i + 1) h
        · have : i + 1 = k' + 1 := by omega
          rw [this, hm]; exact hmpos 0 (by omega)))
    calc (3 ^ oSum o k' * bprod m k') * (3 ^ o k' * m k')
        ≤ (2 ^ blockLen o e k' * bprod (fun i => m (i + 1)) k') * (3 ^ o k' * m k') :=
          Nat.mul_le_mul_right _ h1
      _ < (2 ^ blockLen o e k' * bprod (fun i => m (i + 1)) k') * (2 ^ (o k' + e k') * m (k' + 1)) :=
          Nat.mul_lt_mul_of_pos_left h2 hp
  have hsh := bprod_shift m (k' + 1)
  rw [hm] at hsh
  have hm0 : 0 < m 0 := hmpos 0 (by omega)
  have heq : bprod (fun i => m (i + 1)) (k' + 1) = bprod m (k' + 1) := by
    have : bprod (fun i => m (i + 1)) (k' + 1) * m 0 = bprod m (k' + 1) * m 0 := by
      rw [hsh, Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hm0 this
  rw [heq] at hstrict
  exact Nat.lt_of_mul_lt_mul_right hstrict

/-- **Satz 78b.** Obere Schranke für das Minimum. -/
theorem block_min_upper (k : Nat) (m o e : Nat → Nat) (μ : Nat) (hk : 0 < k)
    (hpos : ∀ i, i < k → 0 < o i)
    (hb : ∀ i, i < k → (∀ j, j < o i → Titer j (m i) % 2 = 1) ∧
      Titer (o i) (m i) = 2 ^ e i * m (i + 1))
    (hm : m k = m 0) (hμ : ∀ i, i < k → μ ≤ m i) :
    (3 ^ oSum o k + 1) * μ ^ k < 3 ^ oSum o k * (μ + 1) ^ k := by
  have h1 := block_growth k m o e hk hpos hb hm
  have h2 := block_min_bound k m o e μ hk hpos hb hm hμ
  calc (3 ^ oSum o k + 1) * μ ^ k ≤ 2 ^ blockLen o e k * μ ^ k := Nat.mul_le_mul_right _ h1
    _ < 3 ^ oSum o k * (μ + 1) ^ k := h2

/-- **Satz 78c.** Ein Zyklus aus einem Block: `m < 3^o`. -/
theorem one_block_min (m o e : Nat) (ho : 0 < o) (hodd : ∀ j, j < o → Titer j m % 2 = 1)
    (hk : Titer o m = 2 ^ e * m) : m < 3 ^ o := by
  have h := block_min_upper 1 (fun _ => m) (fun _ => o) (fun _ => e) m (by decide)
    (fun _ _ => ho) (fun _ _ => ⟨hodd, hk⟩) rfl (fun _ _ => Nat.le_refl _)
  simp only [oSum, Nat.zero_add, Nat.pow_one] at h
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one] at h
  omega

end Collatz
