import Collatz.Reduction

/-!
# Nachgerechnet: alle Zahlen bis zu einer Schranke erreichen die 1

`descendsWithin` folgt der Collatz-Folge, bis sie unter den Startwert fällt.
`descendsWithin_sound` beweist, dass ein `true` wirklich Abstieg bedeutet.
Der Lean-Kernel prüft dann alle Zahlen bis `N` (`decide +kernel`), und mit der
starken Induktion aus `Reduction.lean` folgt: alle `1 ≤ n ≤ N` erreichen die 1.
-/

namespace Collatz

/-- Fällt die Folge ab `x` innerhalb von `fuel` Schritten unter `n`? -/
def descendsWithin (n : Nat) : (fuel : Nat) → (x : Nat) → Bool
  | 0, _ => false
  | f + 1, x => if step x < n then true else descendsWithin n f (step x)

theorem descendsWithin_sound (n : Nat) :
    ∀ f x, descendsWithin n f x = true → ∃ k, iter k x < n := by
  intro f
  induction f with
  | zero => intro x h; simp [descendsWithin] at h
  | succ f ih =>
    intro x h
    unfold descendsWithin at h
    by_cases hc : step x < n
    · exact ⟨1, hc⟩
    · rw [if_neg hc] at h
      obtain ⟨k, hk⟩ := ih _ h
      exact ⟨k + 1, hk⟩

/-- Prüft alle `2 ≤ m ≤ N`. -/
def allDescendUpto (fuel : Nat) : (N : Nat) → Bool
  | 0 => true
  | N + 1 => (N + 1 ≤ 1 || descendsWithin (N + 1) fuel (N + 1)) && allDescendUpto fuel N

theorem descends_of_allDescendUpto {fuel : Nat} :
    ∀ N, allDescendUpto fuel N = true → ∀ m, 1 < m → m ≤ N → Descends m := by
  intro N
  induction N with
  | zero => intro _ m h1 hm; omega
  | succ N ih =>
    intro h m h1 hm
    unfold allDescendUpto at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨hN, hrest⟩ := h
    by_cases hmN : m = N + 1
    · subst hmN
      rcases hN with h' | h'
      · omega
      · exact descendsWithin_sound _ fuel _ h'
    · exact ih hrest m h1 (by omega)

theorem reachesOne_upto_of_check {N fuel : Nat} (h : allDescendUpto fuel N = true) :
    ∀ n, 0 < n → n ≤ N → ReachesOne n :=
  reachesOne_of_descends_upto N (descends_of_allDescendUpto N h)

/-- **Alle Zahlen von 1 bis 10 000 erreichen die 1** (vom Lean-Kernel nachgerechnet). -/
theorem reachesOne_upto_10000 : ∀ n, 0 < n → n ≤ 10000 → ReachesOne n :=
  reachesOne_upto_of_check (N := 10000) (fuel := 300) (by decide +kernel)

/-- Beispiel: die berühmte 27 braucht 111 Schritte und erreicht die 1. -/
theorem iter_111_27 : iter 111 27 = 1 := by decide +kernel

end Collatz
