import Collatz.Counterexample

/-!
# Läufe ungerader Schritte: hier zählt die Grösse

Nach Satz 35/36 reicht 2-adische Information nicht für einen Beweis: Auf `ℤ₂` hat `−1` lauter
ungerade Schritte (`T(−1) = −1`). Für **natürliche** Zahlen ist das unmöglich, und zwar
quantitativ:

* `odd_run_dvd`: Sind `x, T(x), …, T^(j−1)(x)` alle ungerade, so ist `2^j ∣ x + 1`,
  also `2^j ≤ x + 1` (`odd_run_le`). Ein Lauf ungerader Schritte ab `x` ist höchstens
  `log₂(x+1)` lang.
* `mersenne`: Das ist scharf: `T^j(2^j·a − 1) = 3^j·a − 1`. Die Zahl `2^j − 1` macht genau
  `j` ungerade Schritte am Stück und wächst dabei auf `3^j − 1`.
* `not_eventually_odd`, `eventually_even_zero`: Keine Folge einer natürlichen Zahl hat ab
  einem Zeitpunkt nur ungerade Schritte, und nur die 0 hat ab einem Zeitpunkt nur gerade.

Das ist ein (kleines) Beispiel für die Art Argument, die ein Beweis braucht: Es benutzt, dass
`x` endlich ist, nicht nur seine letzten Binärziffern.
-/

namespace Collatz

/-- **Läufe ungerader Schritte.** -/
theorem odd_run_dvd : ∀ j x, (∀ i, i < j → Titer i x % 2 = 1) → 2 ^ j ∣ x + 1 := by
  intro j
  induction j with
  | zero => intro x _; exact Nat.one_dvd _
  | succ j ih =>
    intro x h
    have hx : x % 2 = 1 := h 0 (by omega)
    have hT := ih (T x) (fun i hi => h (i + 1) (by omega))
    obtain ⟨y, hy⟩ : ∃ y, x + 1 = 2 * y := ⟨(x + 1) / 2, by omega⟩
    have hTy : T x + 1 = y * 3 := by unfold T; rw [if_neg (by omega)]; omega
    rw [hTy] at hT
    have hd : 2 ^ j ∣ y := Nat.Coprime.dvd_of_dvd_mul_right (coprime_pow_two_three j) hT
    rw [hy, Nat.pow_succ, Nat.mul_comm (2 ^ j) 2]
    exact Nat.mul_dvd_mul_left 2 hd

theorem odd_run_le {j x : Nat} (h : ∀ i, i < j → Titer i x % 2 = 1) : 2 ^ j ≤ x + 1 :=
  Nat.le_of_dvd (by omega) (odd_run_dvd j x h)

/-- **Mersenne-Zahlen sind scharf.** `T^j(2^j·a − 1) = 3^j·a − 1` für `a ≥ 1`. -/
theorem mersenne : ∀ j a, 0 < a → Titer j (2 ^ j * a - 1) = 3 ^ j * a - 1 := by
  intro j
  induction j with
  | zero => intro a _; simp [Titer]
  | succ j ih =>
    intro a ha
    show Titer j (T (2 ^ (j + 1) * a - 1)) = 3 ^ (j + 1) * a - 1
    have hp : 0 < 2 ^ j * a := Nat.mul_pos (Nat.two_pow_pos j) ha
    have e1 : 2 ^ (j + 1) * a = 2 * (2 ^ j * a) := by rw [Nat.pow_succ]; grind
    have e2 : 2 ^ j * (3 * a) = 3 * (2 ^ j * a) := by grind
    have hT : T (2 ^ (j + 1) * a - 1) = 2 ^ j * (3 * a) - 1 := by
      rw [e1, e2]
      generalize 2 ^ j * a = P at hp ⊢
      unfold T; rw [if_neg (by omega)]; omega
    rw [hT, ih (3 * a) (by omega), Nat.pow_succ, Nat.mul_assoc]

/-- Keine Folge hat ab einem Zeitpunkt nur ungerade Schritte. -/
theorem not_eventually_odd (n s : Nat) : ¬ ∀ i, Titer (s + i) n % 2 = 1 := by
  intro h
  have := odd_run_le (j := Titer s n + 1) (x := Titer s n)
    (fun i _ => by rw [← Titer_add]; exact h i)
  have := @Nat.lt_two_pow_self (Titer s n + 1)
  omega

/-- Nur die 0 hat ab einem Zeitpunkt nur gerade Schritte. -/
theorem eventually_even_zero (n s : Nat) (h : ∀ i, Titer (s + i) n % 2 = 0) : Titer s n = 0 := by
  -- T^i(x) = x / 2^i bei lauter geraden Schritten, also 2^i ∣ x für alle i
  have key : ∀ i x, (∀ l, l < i → Titer l x % 2 = 0) → 2 ^ i ∣ x := by
    intro i
    induction i with
    | zero => intro x _; exact Nat.one_dvd _
    | succ i ih =>
      intro x hx
      have h0 : x % 2 = 0 := hx 0 (by omega)
      have := ih (T x) (fun l hl => hx (l + 1) (by omega))
      have hT : T x = x / 2 := by unfold T; rw [if_pos h0]
      rw [hT] at this
      obtain ⟨c, hc⟩ := this
      have hx2 : x = 2 * (2 ^ i * c) := by omega
      exact ⟨c, by rw [hx2, Nat.pow_succ]; grind⟩
  have hd := key (Titer s n + 1) (Titer s n) (fun l _ => by rw [← Titer_add]; exact h l)
  have := @Nat.lt_two_pow_self (Titer s n + 1)
  rcases Nat.eq_zero_or_pos (Titer s n) with h0 | h0
  · exact h0
  · have := Nat.le_of_dvd h0 hd; omega

end Collatz
