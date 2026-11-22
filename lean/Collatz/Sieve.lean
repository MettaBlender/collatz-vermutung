import Collatz.Reduction

/-!
# Ein verifiziertes Restklassen-Sieb

Idee: Schreibe `n = N·a + r` mit `N = 2^K` und `0 ≤ r < N`. Solange der Koeffizient
vor `a` gerade ist, hängt die Parität des aktuellen Wertes `M·a + s` nur von `s` ab.
Wir können also die ersten Collatz-Schritte für die **ganze Restklasse** auf einmal
symbolisch ausrechnen. Wird dabei `M·a + s` sicher kleiner als `N·a + r`, so fällt
jede Zahl dieser Restklasse ab.

`check` ist ein ausführbarer Algorithmus; `check_sound` beweist, dass er korrekt ist.
Danach lässt der Lean-Kernel `check` für alle Restklassen modulo `2^K` laufen
(`decide`), und wir erhalten eine bewiesene Reduktion der Vermutung auf die wenigen
übrig bleibenden Restklassen.
-/

namespace Collatz

/-- Symbolischer Test: Fällt jede Zahl `N·a + r` ab? Aktueller Wert ist `M·a + s`. -/
def check (N r : Nat) : (fuel : Nat) → (M s : Nat) → Bool
  | 0, _, _ => false
  | f + 1, M, s =>
    if M < N && (s < r || (s ≤ r && r ≤ 1)) then true
    else if M % 2 = 0 then
      if s % 2 = 0 then check N r f (M / 2) (s / 2)
      else check N r f (3 * M) (3 * s + 1)
    else false

theorem step_affine_even {m a s : Nat} (hs : s % 2 = 0) :
    step (2 * m * a + s) = m * a + s / 2 := by
  rw [Nat.mul_assoc]
  rw [step_even (by omega)]
  omega

theorem step_affine_odd {m a s : Nat} (hs : s % 2 = 1) :
    step (2 * m * a + s) = 3 * (2 * m) * a + (3 * s + 1) := by
  rw [Nat.mul_assoc, step_odd (by omega), Nat.mul_assoc, Nat.mul_assoc]
  omega

/-- **Korrektheit des Siebs.** -/
theorem check_sound (N r : Nat) :
    ∀ f M s, check N r f M s = true →
      ∀ a, 1 < N * a + r → ∃ k, iter k (M * a + s) < N * a + r := by
  intro f
  induction f with
  | zero => intro M s h; simp [check] at h
  | succ f ih =>
    intro M s h a ha
    unfold check at h
    by_cases hc : (M < N && (s < r || (s ≤ r && r ≤ 1))) = true
    · refine ⟨0, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hc
      obtain ⟨hMN, hsr⟩ := hc
      simp only [iter_zero]
      rcases hsr with hsr | ⟨hsr, hr⟩
      · have : M * a ≤ N * a := Nat.mul_le_mul_right a (Nat.le_of_lt hMN)
        omega
      · have ha0 : 0 < a := by
          rcases Nat.eq_zero_or_pos a with h0 | h0
          · subst h0; omega
          · exact h0
        have : M * a < N * a := Nat.mul_lt_mul_of_pos_right hMN ha0
        omega
    · rw [if_neg hc] at h
      by_cases hM : M % 2 = 0
      · rw [if_pos hM] at h
        obtain ⟨m, rfl⟩ : ∃ m, M = 2 * m := ⟨M / 2, by omega⟩
        by_cases hs : s % 2 = 0
        · rw [if_pos hs] at h
          have hm : 2 * m / 2 = m := by omega
          rw [hm] at h
          obtain ⟨k, hk⟩ := ih _ _ h a ha
          exact ⟨k + 1, by rw [iter_succ, step_affine_even hs]; exact hk⟩
        · rw [if_neg hs] at h
          obtain ⟨k, hk⟩ := ih _ _ h a ha
          exact ⟨k + 1, by rw [iter_succ, step_affine_odd (by omega)]; exact hk⟩
      · rw [if_neg hM] at h; simp at h

/-- Wenn das Sieb die Restklasse `r mod N` erledigt, fällt jede Zahl darin ab. -/
theorem descends_of_check {N r f : Nat} (h : check N r f N r = true)
    {n : Nat} (hn : n % N = r) (h1 : 1 < n) : Descends n := by
  have hdiv : N * (n / N) + r = n := by rw [← hn]; exact Nat.div_add_mod n N
  obtain ⟨k, hk⟩ := check_sound N r f N r h (n / N) (by omega)
  exact ⟨k, by rw [hdiv] at hk; exact hk⟩

/-- Alle Restklassen `r < N`, die das Sieb **nicht** erledigt. -/
def survivors (N f : Nat) : List Nat :=
  (List.range N).filter (fun r => !check N r f N r)

theorem mem_survivors_of_not_check {N f r : Nat} (hr : r < N) (h : check N r f N r = false) :
    r ∈ survivors N f := by
  simp [survivors, List.mem_filter, List.mem_range, hr, h]

/-- **Allgemeine Sieb-Reduktion**: Es genügt, den Abstieg für die Zahlen in den
übrig bleibenden Restklassen zu zeigen. -/
theorem conjecture_of_survivors (N f : Nat) (hN : 0 < N)
    (h : ∀ n, n % N ∈ survivors N f → Descends n) : CollatzConjecture := by
  apply conjecture_of_descends
  intro n h1
  cases hc : check N (n % N) f N (n % N) with
  | true => exact descends_of_check hc rfl h1
  | false => exact h n (mem_survivors_of_not_check (Nat.mod_lt _ hN) hc)

/-! ## Konkrete, vom Kernel nachgerechnete Ergebnisse -/

/-- Modulo 2^4 = 16 bleiben genau die Restklassen 7, 11, 15. -/
theorem survivors_16 : survivors 16 64 = [7, 11, 15] := by decide

/-- Modulo 2^8 = 256 bleiben nur 19 von 256 Restklassen übrig (7.4 %). -/
theorem survivors_256 :
    survivors 256 64 =
      [27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255] := by
  decide

theorem conjecture_of_descends_mod_256
    (h : ∀ n, n % 256 ∈ [27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207,
      223, 231, 239, 251, 255] → Descends n) : CollatzConjecture :=
  conjecture_of_survivors 256 64 (by decide) (by rw [survivors_256]; exact h)

/-- Modulo 2^12 = 4096 bleiben 226 Restklassen übrig (5.5 %). -/
theorem survivors_4096_length : (survivors 4096 100).length = 226 := by decide +kernel

theorem conjecture_of_descends_mod_4096
    (h : ∀ n, n % 4096 ∈ survivors 4096 100 → Descends n) : CollatzConjecture :=
  conjecture_of_survivors 4096 100 (by decide) h

end Collatz
