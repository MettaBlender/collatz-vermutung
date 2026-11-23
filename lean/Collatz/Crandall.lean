import Collatz.InverseTree

/-!
# Viele Zahlen erreichen die 1: eine untere Schranke für alle `x` (Crandall-Typ)

`InverseTree.lean` zeigt: Über jedem `n` mit `3 ∤ n` liegen unendlich viele ungerade Vorfahren.
Hier machen wir daraus eine **Zählung**. Jeder ungerade Knoten `n` (nicht durch 3 teilbar) hat
zwei *kleine* ungerade Vorfahren `child n false ≠ child n true`, beide wieder nicht durch 3
teilbar, mit `3·c + 1 = 2^E · n`, `E ≤ 6`, also `c < 22·n`.

Ab der Wurzel 5 entsteht so ein binärer Baum `node t k` (`k < 2^t` codiert den Weg):

* `node_reachesOne`: jeder Knoten erreicht die 1,
* `node_le`: `node t k ≤ 5 · 22^t`,
* `node_injective`: verschiedene Wege geben verschiedene Zahlen (Eindeutigkeit des ungeraden
  Anteils: `2^a·n = 2^b·m` mit `n, m` ungerade ⇒ `n = m`).

**Folgerung:** Unter den Zahlen `≤ 5·22^t` erreichen mindestens `2^t` die 1, d. h. für jedes `x`
mindestens etwa `(x/5)^0.22` Zahlen `≤ x`. Das ist eine (schwache) Form des Satzes von
Crandall (1978); Krasikov und Lagarias kommen mit viel feineren Methoden auf `x^0.84`.
Die Vermutung würde `x` verlangen. Der Satz gilt für **alle** `t`, ohne Rechnung.
-/

namespace Collatz

/-- Der kleinste ungerade Vorfahre: `(4n−1)/3` für `n ≡ 1`, `(2n−1)/3` für `n ≡ 2 (mod 3)`. -/
def firstAnc (n : Nat) : Nat := if n % 3 = 1 then (4 * n - 1) / 3 else (2 * n - 1) / 3

/-- Die zwei Kinder: von `firstAnc, 4·firstAnc+1, 16·firstAnc+5` ist genau eines durch 3 teilbar; die anderen
beiden sind die Kinder. -/
def child (n : Nat) (b : Bool) : Nat :=
  if b then (if firstAnc n % 3 = 1 then 4 * firstAnc n + 1 else 16 * firstAnc n + 5)
  else (if firstAnc n % 3 = 0 then 4 * firstAnc n + 1 else firstAnc n)

/-- Eigenschaften von `firstAnc`: `3·firstAnc + 1 = 4n` bzw. `2n`, `firstAnc` ungerade. -/
theorem firstAnc_spec {n : Nat} (h1 : n % 2 = 1) (h3 : n % 3 ≠ 0) :
    firstAnc n % 2 = 1 ∧ ((n % 3 = 1 ∧ 3 * firstAnc n + 1 = 4 * n) ∨ (n % 3 = 2 ∧ 3 * firstAnc n + 1 = 2 * n)) := by
  unfold firstAnc
  by_cases h : n % 3 = 1
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- **Ein Kind.** `child n b` ist ungerade, nicht durch 3 teilbar, und `3·c + 1 = 2^E · n` mit
`1 ≤ E ≤ 6`. -/
theorem child_spec {n : Nat} (h1 : n % 2 = 1) (h3 : n % 3 ≠ 0) (b : Bool) :
    child n b % 2 = 1 ∧ child n b % 3 ≠ 0 ∧ ∃ E, E ≤ 6 ∧ 3 * child n b + 1 = 2 ^ E * n := by
  obtain ⟨hc1, hc⟩ := firstAnc_spec h1 h3
  unfold child
  generalize firstAnc n = c at hc1 hc
  have p1 : (2 : Nat) ^ 1 = 2 := rfl
  have p2 : (2 : Nat) ^ 2 = 4 := rfl
  have p3 : (2 : Nat) ^ 3 = 8 := rfl
  have p4 : (2 : Nat) ^ 4 = 16 := rfl
  have p5 : (2 : Nat) ^ 5 = 32 := rfl
  have p6 : (2 : Nat) ^ 6 = 64 := rfl
  cases b with
  | true =>
    simp only [if_true]
    by_cases hr : c % 3 = 1
    · rw [if_pos hr]
      rcases hc with ⟨_, h⟩ | ⟨_, h⟩
      · exact ⟨by omega, by omega, 4, by omega, by rw [p4]; omega⟩
      · exact ⟨by omega, by omega, 3, by omega, by rw [p3]; omega⟩
    · rw [if_neg hr]
      rcases hc with ⟨_, h⟩ | ⟨_, h⟩
      · exact ⟨by omega, by omega, 6, by omega, by rw [p6]; omega⟩
      · exact ⟨by omega, by omega, 5, by omega, by rw [p5]; omega⟩
  | false =>
    simp only [Bool.false_eq_true, if_false]
    by_cases hr : c % 3 = 0
    · rw [if_pos hr]
      rcases hc with ⟨_, h⟩ | ⟨_, h⟩
      · exact ⟨by omega, by omega, 4, by omega, by rw [p4]; omega⟩
      · exact ⟨by omega, by omega, 3, by omega, by rw [p3]; omega⟩
    · rw [if_neg hr]
      rcases hc with ⟨_, h⟩ | ⟨_, h⟩
      · exact ⟨by omega, by omega, 2, by omega, by rw [p2]; omega⟩
      · exact ⟨by omega, by omega, 1, by omega, by rw [p1]; omega⟩

/-- Die beiden Kinder sind verschieden. -/
theorem child_ne {n : Nat} : child n false ≠ child n true := by
  unfold child
  simp only [Bool.false_eq_true, if_false, if_true]
  generalize firstAnc n = c
  by_cases h0 : c % 3 = 0
  · rw [if_pos h0, if_neg (by omega)]; omega
  · rw [if_neg h0]
    by_cases h1 : c % 3 = 1
    · rw [if_pos h1]; omega
    · rw [if_neg h1]; omega

/-- Ein Kind ist kleiner als `22 n`. -/
theorem child_lt {n : Nat} (h1 : n % 2 = 1) (h3 : n % 3 ≠ 0) (b : Bool) :
    child n b < 22 * n := by
  obtain ⟨_, _, E, hE, h⟩ := child_spec h1 h3 b
  have : 2 ^ E ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) hE
  have : 2 ^ E * n ≤ 64 * n := Nat.mul_le_mul_right n this
  omega

/-- Die Folge eines Kindes erreicht den Elternknoten. -/
theorem child_reaches {n : Nat} (h1 : n % 2 = 1) (h3 : n % 3 ≠ 0) (b : Bool) :
    ∃ j, iter j (child n b) = n := by
  obtain ⟨hc, _, E, _, h⟩ := child_spec h1 h3 b
  refine ⟨1 + E, ?_⟩
  rw [iter_add]
  have : iter 1 (child n b) = 2 ^ E * n := by
    show step (child n b) = 2 ^ E * n
    rw [step_odd hc, h]
  rw [this, iter_double_pow]

/-- **Eindeutigkeit des ungeraden Anteils.** -/
theorem odd_part_unique : ∀ a b n m, n % 2 = 1 → m % 2 = 1 → 2 ^ a * n = 2 ^ b * m → n = m := by
  intro a
  induction a with
  | zero =>
    intro b n m hn hm h
    cases b with
    | zero => simpa using h
    | succ b =>
      rw [Nat.pow_zero, Nat.one_mul, Nat.pow_succ, Nat.mul_comm (2 ^ b) 2, Nat.mul_assoc] at h
      omega
  | succ a ih =>
    intro b n m hn hm h
    cases b with
    | zero =>
      rw [Nat.pow_zero, Nat.one_mul, Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc] at h
      omega
    | succ b =>
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_comm (2 ^ b) 2,
        Nat.mul_assoc, Nat.mul_assoc] at h
      exact ih b n m hn hm (by omega)

/-- Gleiche Kinder haben gleiche Eltern. -/
theorem child_parent_eq {n m : Nat} (hn1 : n % 2 = 1) (hn3 : n % 3 ≠ 0) (hm1 : m % 2 = 1)
    (hm3 : m % 3 ≠ 0) {b b' : Bool} (h : child n b = child m b') : n = m := by
  obtain ⟨_, _, E, _, hE⟩ := child_spec hn1 hn3 b
  obtain ⟨_, _, E', _, hE'⟩ := child_spec hm1 hm3 b'
  rw [h] at hE
  exact odd_part_unique E E' n m hn1 hm1 (by omega)

/-- Der Baum: `node 0 k = 5`, `node (t+1) k = child (node t (k/2)) (Bit 0 von k)`. -/
def node : Nat → Nat → Nat
  | 0, _ => 5
  | t + 1, k => child (node t (k / 2)) (k % 2 == 1)

/-- Jeder Knoten ist ungerade und nicht durch 3 teilbar. -/
theorem node_spec : ∀ t k, node t k % 2 = 1 ∧ node t k % 3 ≠ 0 := by
  intro t
  induction t with
  | zero => intro k; show 5 % 2 = 1 ∧ 5 % 3 ≠ 0; decide
  | succ t ih =>
    intro k
    obtain ⟨h1, h3⟩ := ih (k / 2)
    obtain ⟨c1, c3, _⟩ := child_spec h1 h3 (k % 2 == 1)
    exact ⟨c1, c3⟩

/-- **Jeder Knoten erreicht die 1.** -/
theorem node_reachesOne : ∀ t k, ReachesOne (node t k) := by
  intro t
  induction t with
  | zero => intro k; exact ⟨5, by show iter 5 5 = 1; decide⟩
  | succ t ih =>
    intro k
    obtain ⟨h1, h3⟩ := node_spec t (k / 2)
    obtain ⟨j, hj⟩ := child_reaches h1 h3 (k % 2 == 1)
    obtain ⟨i, hi⟩ := ih (k / 2)
    exact ⟨j + i, by show iter (j + i) (child (node t (k / 2)) (k % 2 == 1)) = 1
                     rw [iter_add, hj, hi]⟩

/-- **Grössenschranke.** `node t k ≤ 5 · 22^t`. -/
theorem node_le : ∀ t k, node t k ≤ 5 * 22 ^ t := by
  intro t
  induction t with
  | zero => intro k; exact Nat.le_refl 5
  | succ t ih =>
    intro k
    obtain ⟨h1, h3⟩ := node_spec t (k / 2)
    have hc := child_lt h1 h3 (k % 2 == 1)
    have := ih (k / 2)
    show child (node t (k / 2)) (k % 2 == 1) ≤ 5 * 22 ^ (t + 1)
    rw [Nat.pow_succ]
    have : 22 * node t (k / 2) ≤ 22 * (5 * 22 ^ t) := Nat.mul_le_mul_left 22 this
    have e : 22 * (5 * 22 ^ t) = 5 * (22 ^ t * 22) := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    omega

/-- **Injektivität.** Verschiedene Wege `k ≠ k' < 2^t` geben verschiedene Zahlen. -/
theorem node_injective : ∀ t k k', k < 2 ^ t → k' < 2 ^ t → node t k = node t k' → k = k' := by
  intro t
  induction t with
  | zero => intro k k' hk hk' _; simp at hk hk'; omega
  | succ t ih =>
    intro k k' hk hk' h
    obtain ⟨h1, h3⟩ := node_spec t (k / 2)
    obtain ⟨h1', h3'⟩ := node_spec t (k' / 2)
    have hp : node t (k / 2) = node t (k' / 2) := child_parent_eq h1 h3 h1' h3' h
    rw [Nat.pow_succ] at hk hk'
    have hq : k / 2 = k' / 2 := ih _ _ (by omega) (by omega) hp
    have hb : (k % 2 == 1) = (k' % 2 == 1) := by
      have h' : child (node t (k / 2)) (k % 2 == 1) = child (node t (k / 2)) (k' % 2 == 1) := by
        have := h; simp only [node] at this; rw [hp] at this ⊢; exact this
      revert h'
      cases (k % 2 == 1) <;> cases (k' % 2 == 1) <;> intro h'
      · rfl
      · exact absurd h' child_ne
      · exact absurd h'.symm child_ne
      · rfl
    have hm : k % 2 = k' % 2 := by
      have a := Nat.mod_two_eq_zero_or_one k
      have b := Nat.mod_two_eq_zero_or_one k'
      rcases a with a | a <;> rcases b with b | b <;> rw [a, b] at hb <;> simp_all
    omega

/-- **Satz (Crandall-Typ, für alle `t`).** Es gibt `2^t` verschiedene Zahlen `≤ 5·22^t`, die
alle die 1 erreichen: die Werte `node t k` für `k < 2^t`. -/
theorem many_reach_one (t : Nat) :
    (∀ k, k < 2 ^ t → node t k ≤ 5 * 22 ^ t ∧ ReachesOne (node t k)) ∧
    (∀ k k', k < 2 ^ t → k' < 2 ^ t → node t k = node t k' → k = k') :=
  ⟨fun k _ => ⟨node_le t k, node_reachesOne t k⟩, node_injective t⟩

end Collatz
