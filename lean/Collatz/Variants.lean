import Collatz.Basic

/-!
# Varianten `qn+1`: für `5n+1` ist die analoge Vermutung falsch

Ersetzt man `3n+1` durch `5n+1`, gibt es einen zweiten Zyklus

    13 → 66 → 33 → 166 → 83 → 416 → 208 → 104 → 52 → 26 → 13,

und die 13 erreicht die 1 nie. Jeder Beweis der Collatz-Vermutung muss also benutzen,
dass der Faktor genau 3 ist (heuristisch: mittlerer Faktor 3/4 < 1, bei 5n+1 aber 5/4 > 1).
-/

namespace Collatz

/-- Ein Schritt der Variante `qn+1`. -/
def stepQ (q n : Nat) : Nat := if n % 2 = 0 then n / 2 else q * n + 1

def iterQ (q : Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iterQ q k (stepQ q n)

/-- Für `q = 3` ist das genau die Collatz-Abbildung. -/
theorem stepQ_three : stepQ 3 = step := rfl

/-- Der Zyklus der 13 unter `5n+1`. -/
def cycle13 : List Nat := [13, 66, 33, 166, 83, 416, 208, 104, 52, 26]

theorem cycle13_closed : ∀ m ∈ cycle13, stepQ 5 m ∈ cycle13 := by decide

theorem iterQ_cycle13 : ∀ k m, m ∈ cycle13 → iterQ 5 k m ∈ cycle13 := by
  intro k
  induction k with
  | zero => intro m hm; exact hm
  | succ k ih => intro m hm; exact ih _ (cycle13_closed m hm)

theorem iterQ_ten_13 : iterQ 5 10 13 = 13 := by decide

/-- **Unter `5n+1` erreicht die 13 nie die 1.** -/
theorem five_not_reachesOne_13 : ∀ k, iterQ 5 k 13 ≠ 1 := by
  intro k h
  have := iterQ_cycle13 k 13 (by decide)
  rw [h] at this
  exact absurd this (by decide)

/-- Auch die 17 liegt unter `5n+1` auf einem eigenen Zyklus. -/
theorem iterQ_17 : iterQ 5 10 17 = 17 := by decide

/-- Zum Vergleich: Für `q = 1` (also `n+1` statt `3n+1`) ist die analoge Vermutung
leicht zu beweisen, weil `n → n+1 → (n+1)/2` immer kleiner wird. -/
theorem one_reachesOne : ∀ n, 0 < n → ∃ k, iterQ 1 k n = 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro h0
    by_cases h1 : n = 1
    · exact ⟨0, h1⟩
    by_cases he : n % 2 = 0
    · have hs : stepQ 1 n = n / 2 := by simp [stepQ, he]
      obtain ⟨k, hk⟩ := ih (n / 2) (by omega) (by omega)
      exact ⟨k + 1, by simp only [iterQ, hs, hk]⟩
    · have hs1 : stepQ 1 n = n + 1 := by simp [stepQ, he]
      have hs2 : stepQ 1 (n + 1) = (n + 1) / 2 := by simp [stepQ]; omega
      obtain ⟨k, hk⟩ := ih ((n + 1) / 2) (by omega) (by omega)
      exact ⟨k + 2, by simp only [iterQ, hs1, hs2, hk]⟩

end Collatz
