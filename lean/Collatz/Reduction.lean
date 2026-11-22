import Collatz.Basic

/-!
# Reduktionen: Es genügt zu zeigen, dass jede Zahl irgendwann kleiner wird

Hauptergebnis: Wenn jede Zahl `n > 1` irgendwann unter ihren Startwert fällt
("endliche Stoppzeit"), dann gilt die Collatz-Vermutung. Danach schränken wir
die zu prüfenden Zahlen auf bestimmte Restklassen ein.
-/

namespace Collatz

/-- `n` fällt irgendwann unter seinen Startwert. -/
def Descends (n : Nat) : Prop := ∃ k, iter k n < n

/-- **Reduktion auf Abstieg**: Fällt jede Zahl `n > 1` irgendwann unter `n`,
dann erreicht jede positive Zahl die 1 (starke Induktion). -/
theorem conjecture_of_descends (h : ∀ n, 1 < n → Descends n) : CollatzConjecture := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst h1; exact reachesOne_one
    · obtain ⟨k, hk⟩ := h n (by omega)
      exact reachesOne_of_iter (ih _ hk (iter_pos hn k))

/-- Lokale Version: Fällt jede Zahl `1 < m ≤ N` ab, dann erreichen alle `0 < m ≤ N` die 1. -/
theorem reachesOne_of_descends_upto (N : Nat) (h : ∀ m, 1 < m → m ≤ N → Descends m) :
    ∀ n, 0 < n → n ≤ N → ReachesOne n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn hN
    by_cases h1 : n = 1
    · subst h1; exact reachesOne_one
    · obtain ⟨k, hk⟩ := h n (by omega) hN
      exact reachesOne_of_iter (ih _ hk (iter_pos hn k) (by omega))

/-- Gerade Zahlen fallen sofort ab. -/
theorem descends_of_even {n : Nat} (h0 : 0 < n) (h : n % 2 = 0) : Descends n :=
  ⟨1, step_lt_of_even h0 h⟩

/-- Zahlen der Form `4a+1` mit `a ≥ 1` fallen nach 3 Schritten ab:
`4a+1 → 12a+4 → 6a+2 → 3a+1`. -/
theorem iter_three_of_mod_four_eq_one (a : Nat) : iter 3 (4 * a + 1) = 3 * a + 1 := by
  have e1 : step (4 * a + 1) = 12 * a + 4 := by rw [step_odd (by omega)]; omega
  have e2 : step (12 * a + 4) = 6 * a + 2 := by rw [step_even (by omega)]; omega
  have e3 : step (6 * a + 2) = 3 * a + 1 := by rw [step_even (by omega)]; omega
  simp only [iter_succ, iter_zero, e1, e2, e3]

theorem descends_of_mod_four_eq_one {n : Nat} (h1 : 1 < n) (h : n % 4 = 1) : Descends n := by
  refine ⟨3, ?_⟩
  have hn : n = 4 * (n / 4) + 1 := by omega
  rw [hn, iter_three_of_mod_four_eq_one]; omega

/-- **Reduktion auf `n ≡ 3 (mod 4)`**. -/
theorem conjecture_of_descends_mod_four (h : ∀ n, n % 4 = 3 → Descends n) :
    CollatzConjecture := by
  apply conjecture_of_descends
  intro n hn
  have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases this with h0 | h0 | h0 | h0
  · exact descends_of_even (by omega) (by omega)
  · exact descends_of_mod_four_eq_one hn h0
  · exact descends_of_even (by omega) (by omega)
  · exact h n h0

/-- `16a+3 → 48a+10 → 24a+5 → 72a+16 → 36a+8 → 18a+4 → 9a+2`. -/
theorem iter_six_of_mod_sixteen_eq_three (a : Nat) : iter 6 (16 * a + 3) = 9 * a + 2 := by
  have e1 : step (16 * a + 3) = 48 * a + 10 := by rw [step_odd (by omega)]; omega
  have e2 : step (48 * a + 10) = 24 * a + 5 := by rw [step_even (by omega)]; omega
  have e3 : step (24 * a + 5) = 72 * a + 16 := by rw [step_odd (by omega)]; omega
  have e4 : step (72 * a + 16) = 36 * a + 8 := by rw [step_even (by omega)]; omega
  have e5 : step (36 * a + 8) = 18 * a + 4 := by rw [step_even (by omega)]; omega
  have e6 : step (18 * a + 4) = 9 * a + 2 := by rw [step_even (by omega)]; omega
  simp only [iter_succ, iter_zero, e1, e2, e3, e4, e5, e6]

theorem descends_of_mod_sixteen_eq_three {n : Nat} (h : n % 16 = 3) : Descends n := by
  refine ⟨6, ?_⟩
  have hn : n = 16 * (n / 16) + 3 := by omega
  rw [hn, iter_six_of_mod_sixteen_eq_three]; omega

/-- **Reduktion auf `n ≡ 7, 11, 15 (mod 16)`**: nur noch 3 von 16 Restklassen sind offen. -/
theorem conjecture_of_descends_mod_sixteen
    (h : ∀ n, (n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15) → Descends n) :
    CollatzConjecture := by
  apply conjecture_of_descends_mod_four
  intro n hn
  have : n % 16 = 3 ∨ n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15 := by omega
  rcases this with h0 | h0 | h0 | h0
  · exact descends_of_mod_sixteen_eq_three h0
  · exact h n (by omega)
  · exact h n (by omega)
  · exact h n (by omega)

/-- Für ungerade `n` gilt `iter 3 (4n+1) = step n`: `4n+1` und `n` laufen zusammen. -/
theorem iter_three_four_mul_add_one {n : Nat} (h : n % 2 = 1) :
    iter 3 (4 * n + 1) = step n := by
  rw [iter_three_of_mod_four_eq_one, step_odd h]

theorem reachesOne_four_mul_add_one_iff {n : Nat} (h : n % 2 = 1) :
    ReachesOne (4 * n + 1) ↔ ReachesOne n := by
  have hn1 : n ≠ 1 ∨ n = 1 := by omega
  constructor
  · intro hr
    have h4 : ReachesOne (iter 3 (4 * n + 1)) := by
      -- 4n+1 ≠ 1, 12n+4 ≠ 1, 6n+2 ≠ 1: drei Schritte zurückverfolgen
      have s1 := reachesOne_step (by omega) hr
      have e1 : step (4 * n + 1) = 12 * n + 4 := by rw [step_odd (by omega)]; omega
      rw [e1] at s1
      have s2 := reachesOne_step (by omega) s1
      have e2 : step (12 * n + 4) = 6 * n + 2 := by rw [step_even (by omega)]; omega
      rw [e2] at s2
      have s3 := reachesOne_step (by omega) s2
      have e3 : step (6 * n + 2) = 3 * n + 1 := by rw [step_even (by omega)]; omega
      rw [e3] at s3
      rwa [iter_three_of_mod_four_eq_one]
    rw [iter_three_four_mul_add_one h] at h4
    exact reachesOne_of_step h4
  · intro hr
    rcases hn1 with hne | heq
    · exact reachesOne_of_iter (k := 3) (by rw [iter_three_four_mul_add_one h]; exact reachesOne_step hne hr)
    · subst heq; exact reachesOne_of_iter (k := 3) (by rw [iter_three_four_mul_add_one h]; exact ⟨2, by decide⟩)

end Collatz
