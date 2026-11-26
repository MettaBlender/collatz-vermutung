import Collatz.OddRuns
import Collatz.Mod6Orbit

/-!
# Satz 69: Die Fenster-Barriere

Die Sätze 32 und 64–68 benutzen vom Bahnminimum `m` nur endlich viel: Um eine Aussage über die
ersten `J` Schritte zu bekommen, braucht man nur `m ≤ x_k` für `k ≤ J`. Hier wird gezeigt, dass
diese endliche Bedingung für jedes `J` und jede Schranke `B` erfüllbar ist:

  Für alle `J, B` gibt es `m ≥ B` mit `m ≤ T^k(m)` für alle `k ≤ J`

(nämlich `m = 2^J·(B+1) − 1`, das `J`-mal hintereinander steigt). Folgerung: Keine Aussage, die nur
aus solchen endlichen Fenstern gewonnen wird, kann je einen Widerspruch liefern. Ein Beweis der
Vermutung muss die ganze unendliche Bahn benutzen, oder zusätzliche Struktur, die über
Paritäts- und Restklassenzählungen hinausgeht. Das erklärt ehrlich, warum die Sätze 64–68 zwar
einen immer schärferen Steckbrief liefern, aber keinen Widerspruch.
-/

namespace Collatz

theorem window_min_exists (J B : Nat) :
    ∃ m, B ≤ m ∧ ∀ k, k ≤ J → m ≤ Titer k m := by
  refine ⟨2 ^ J * (B + 1) - 1, ?_, ?_⟩
  · have : B + 1 ≤ 2 ^ J * (B + 1) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos J)
    omega
  · intro k hk
    obtain ⟨d, rfl⟩ : ∃ d, J = k + d := ⟨J - k, by omega⟩
    have ha : 0 < 2 ^ d * (B + 1) := Nat.mul_pos (Nat.two_pow_pos d) (by omega)
    have e : 2 ^ (k + d) * (B + 1) = 2 ^ k * (2 ^ d * (B + 1)) := by
      rw [Nat.pow_add, Nat.mul_assoc]
    rw [e, mersenne k _ ha]
    have h23 : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by omega) k
    have := Nat.mul_le_mul_right (2 ^ d * (B + 1)) h23
    omega

/-- Dieselben Fenster-Zahlen erfüllen auch die Dichteschranke von Satz 32 im Fenster:
mehr als 5/8 ungerade Schritte (hier sogar lauter ungerade). -/
theorem window_min_all_odd (J B : Nat) (k : Nat) (hk : k < J) :
    Titer k (2 ^ J * (B + 1) - 1) % 2 = 1 := by
  obtain ⟨d, rfl⟩ : ∃ d, J = k + (d + 1) := ⟨J - k - 1, by omega⟩
  have ha : 0 < 2 ^ (d + 1) * (B + 1) := Nat.mul_pos (Nat.two_pow_pos _) (by omega)
  have e : 2 ^ (k + (d + 1)) * (B + 1) = 2 ^ k * (2 ^ (d + 1) * (B + 1)) := by
    rw [Nat.pow_add, Nat.mul_assoc]
  rw [e, mersenne k _ ha]
  have hp : 0 < 3 ^ k := Nat.pow_pos (by omega)
  rw [Nat.pow_succ, show 3 ^ k * (2 ^ d * 2 * (B + 1)) = 2 * (3 ^ k * 2 ^ d * (B + 1)) by grind]
  have : 0 < 3 ^ k * 2 ^ d * (B + 1) :=
    Nat.mul_pos (Nat.mul_pos hp (Nat.two_pow_pos d)) (by omega)
  omega

end Collatz
