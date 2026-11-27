import Collatz.TwoBlockShape

/-!
# Satz 75: Das Blocksystem eines beliebigen Zyklus

Verallgemeinerung von Satz 73 (ein Block) und Satz 74 (zwei Blöcke) auf **beliebig viele** Blöcke.
Ein `k`-Zyklus besteht aus ungeraden Startwerten `m₀, m₁, …, m_k = m₀`; im Block `i` führen
`oᵢ` Aufstiege von `mᵢ` zu `2^eᵢ · m_{i+1}`, danach `eᵢ` Halbierungen zu `m_{i+1}`.

Für alle `k` und alle Blocklängen gilt:

* Der Zyklus schliesst sich nach `L = Σ (oᵢ + eᵢ)` Schritten: `Titer L m₀ = m₀`.
* Mit `tᵢ = (mᵢ + 1) / 2^oᵢ` ist `mᵢ + 1 = 2^oᵢ · tᵢ`, `tᵢ ≥ 1`, und es gilt das
  **zyklische lineare System**
  `2^(eᵢ + o_{i+1}) · t_{i+1} + 1 = 3^oᵢ · tᵢ + 2^eᵢ`  für alle `i < k`.

Jeder Collatz-Zyklus ist also eine positive ganzzahlige Lösung eines solchen Systems; umgekehrt
legt das System den Zyklus fest. Damit ist die Zyklenfrage exakt auf ein lineares
diophantisches Problem in den `tᵢ` zurückgeführt.
-/

namespace Collatz

/-- Gesamtlänge der ersten `j` Blöcke. -/
def blockLen (o e : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => blockLen o e j + (o j + e j)

/-- **Satz 75.** -/
theorem block_system (k : Nat) (m o e : Nat → Nat) (hk : 0 < k)
    (hb : ∀ i, i < k → (∀ j, j < o i → Titer j (m i) % 2 = 1) ∧
      Titer (o i) (m i) = 2 ^ e i * m (i + 1))
    (hm : m k = m 0) (ho : o k = o 0) :
    Titer (blockLen o e k) (m 0) = m 0 ∧
    (∀ i, i ≤ k → m i + 1 = 2 ^ o i * ((m i + 1) / 2 ^ o i) ∧ 1 ≤ (m i + 1) / 2 ^ o i) ∧
    (∀ i, i < k → 2 ^ (e i + o (i + 1)) * ((m (i + 1) + 1) / 2 ^ o (i + 1)) + 1
        = 3 ^ o i * ((m i + 1) / 2 ^ o i) + 2 ^ e i) := by
  -- Abschluss
  have hclose : ∀ j, j ≤ k → Titer (blockLen o e j) (m 0) = m j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      obtain ⟨_, hk'⟩ := hb j (by omega)
      show Titer (blockLen o e j + (o j + e j)) (m 0) = m (j + 1)
      rw [Titer_add, ih (by omega), Titer_add, hk', st_halve]
  -- t-Darstellung für i < k
  have hrep : ∀ i, i < k → m i + 1 = 2 ^ o i * ((m i + 1) / 2 ^ o i) ∧
      1 ≤ (m i + 1) / 2 ^ o i ∧
      2 ^ e i * m (i + 1) + 1 = 3 ^ o i * ((m i + 1) / 2 ^ o i) := by
    intro i hi
    obtain ⟨hodd, hki⟩ := hb i hi
    obtain ⟨t, ht1, ht, h2⟩ := tbs_block (m i) (m (i + 1)) (o i) (e i) hodd hki
    have hpos : 0 < 2 ^ o i := Nat.pow_pos (by decide)
    have hdiv : (m i + 1) / 2 ^ o i = t := by
      rw [ht, Nat.mul_div_cancel_left _ hpos]
    rw [hdiv]
    exact ⟨ht, ht1, h2⟩
  have hrep' : ∀ i, i ≤ k → m i + 1 = 2 ^ o i * ((m i + 1) / 2 ^ o i) ∧
      1 ≤ (m i + 1) / 2 ^ o i := by
    intro i hi
    rcases Nat.lt_or_ge i k with h | h
    · exact ⟨(hrep i h).1, (hrep i h).2.1⟩
    · have : i = k := by omega
      subst this
      rw [hm, ho]
      exact ⟨(hrep 0 hk).1, (hrep 0 hk).2.1⟩
  refine ⟨by rw [hclose k (Nat.le_refl _), hm], hrep', ?_⟩
  intro i hi
  obtain ⟨_, _, h2⟩ := hrep i hi
  obtain ⟨hn, _⟩ := hrep' (i + 1) (by omega)
  generalize (m (i + 1) + 1) / 2 ^ o (i + 1) = s at hn ⊢
  generalize (m i + 1) / 2 ^ o i = t at h2 ⊢
  have : 2 ^ e i * (m (i + 1) + 1) = 2 ^ (e i + o (i + 1)) * s := by
    rw [hn, Nat.pow_add, Nat.mul_assoc]
  rw [Nat.mul_add, Nat.mul_one] at this
  omega

end Collatz
