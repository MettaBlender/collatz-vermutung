import Collatz.Sieve20
import Collatz.Verified

/-!
# Nachgerechnet bis 2^22 mit Hilfe des Siebs

Eine Zahl `m` fällt sicher unter sich selbst, wenn ihre Restklasse modulo `2^16` vom Sieb
erledigt wird (`descends_of_check`). Der Kernel muss also nur die Zahlen
`m = 2^16·a + r` mit `r` in einer der 2114 offenen Klassen nachrechnen: für `m < 2^22`
sind das 2114 · 64 = 135 296 statt 4 194 304 Zahlen.

Die Rechnung steht in 64 Blöcken in `VerifiedHugeA` bis `VerifiedHugeH`; zusammengesetzt
wird sie in `VerifiedHugeAll`.
-/

namespace Collatz

/-- Schneller Abstiegstest: ein ungerader Schritt wird gleich mit dem folgenden Halbieren
zusammengefasst (`x ↦ (3x+1)/2`); nach einem solchen Doppelschritt ist der Wert grösser. -/
def fastDescends (n : Nat) : (fuel x : Nat) → Bool
  | 0, _ => false
  | f + 1, x =>
    if x % 2 = 0 then (if x / 2 < n then true else fastDescends n f (x / 2))
    else fastDescends n f ((3 * x + 1) / 2)

theorem iter_two_odd {x : Nat} (h : x % 2 = 1) : iter 2 x = (3 * x + 1) / 2 := by
  have e1 : step x = 3 * x + 1 := step_odd h
  have e2 : step (3 * x + 1) = (3 * x + 1) / 2 := step_even (by omega)
  simp only [iter_succ, iter_zero, e1, e2]

theorem fastDescends_sound (n : Nat) :
    ∀ f x, fastDescends n f x = true → ∃ k, iter k x < n := by
  intro f
  induction f with
  | zero => intro x h; simp [fastDescends] at h
  | succ f ih =>
    intro x h
    unfold fastDescends at h
    by_cases hx : x % 2 = 0
    · rw [if_pos hx] at h
      have e : iter 1 x = x / 2 := by simp only [iter_succ, iter_zero, step_even hx]
      by_cases hl : x / 2 < n
      · exact ⟨1, by rw [e]; exact hl⟩
      · rw [if_neg hl] at h
        obtain ⟨k, hk⟩ := ih _ h
        exact ⟨1 + k, by rw [iter_add, e]; exact hk⟩
    · rw [if_neg hx] at h
      obtain ⟨k, hk⟩ := ih _ h
      exact ⟨2 + k, by rw [iter_add, iter_two_odd (by omega)]; exact hk⟩

/-- Prüft, dass jede Zahl `N·a + r > 1` mit `a < A` abfällt. -/
def verifyClass (N r fuel : Nat) : (A : Nat) → Bool
  | 0 => true
  | A + 1 =>
    (N * A + r ≤ 1 || fastDescends (N * A + r) fuel (N * A + r)) && verifyClass N r fuel A

theorem descends_of_verifyClass {N r fuel : Nat} :
    ∀ A, verifyClass N r fuel A = true → ∀ a, a < A → 1 < N * a + r → Descends (N * a + r) := by
  intro A
  induction A with
  | zero => intro _ a ha; omega
  | succ A ih =>
    intro h a ha h1
    unfold verifyClass at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨hA, hrest⟩ := h
    by_cases haA : a = A
    · subst haA
      rcases hA with h' | h'
      · omega
      · exact fastDescends_sound _ fuel _ h'
    · exact ih hrest a (by omega) h1

/-- Prüft alle offenen Klassen `lo ≤ r < lo + len` modulo `N` für die Vielfachen `a < A`. -/
def verifyOpen (N f fuel lo len A : Nat) : Bool :=
  (openIn N f lo len).all (fun r => verifyClass N r fuel A)

theorem descends_of_verifyOpen {N f fuel lo len A : Nat} (h : verifyOpen N f fuel lo len A = true)
    {m : Nat} (hlo : lo ≤ m % N) (hhi : m % N < lo + len) (hm : m < N * A)
    (h1 : 1 < m) : Descends m := by
  cases hc : check N (m % N) f N (m % N) with
  | true => exact descends_of_check hc rfl h1
  | false =>
    have hmem := mem_openIn hc len lo hlo hhi
    unfold verifyOpen at h
    rw [List.all_eq_true] at h
    have hv := h _ hmem
    have hdecomp : N * (m / N) + m % N = m := Nat.div_add_mod m N
    have ha : m / N < A := Nat.div_lt_of_lt_mul hm
    have := descends_of_verifyClass A hv (m / N) ha (by rw [hdecomp]; exact h1)
    rwa [hdecomp] at this

end Collatz
