import Collatz.Mod3Orbit

/-!
# Satz 68: Mehr als 26 % der Bahnglieder eines Gegenbeispiels sind ≡ 5 modulo 6

Satz 65 und Satz 67 zusammengesetzt: Ist `x_i ≡ 3 (mod 4)`, so ist `x_{i+1} = (3x_i+1)/2`
ungerade (Satz 65) und `≡ 2 (mod 3)` (Satz 67), also `x_{i+1} ≡ 5 (mod 6)`. Darum gibt es
unter `x_1, …, x_J` mindestens so viele Glieder `≡ 5 (mod 6)` wie Stellen `i < J` mit
`x_i ≡ 3 (mod 4)`. Mit Satz 66 folgt für das kleinste Glied `m ≥ 2^27` eines Gegenbeispiels:
`17·J ≤ 65·(#{1 ≤ i ≤ J : x_i ≡ 5 mod 6} + 1)`.

Ehrliche Einordnung: Das ist eine weitere Steckbrief-Eigenschaft (gemeinsame Verteilung modulo 2
und 3), kein Widerspruch. Eine Zahl ohne Faktor 2 und 3 läge «zufällig» je zur Hälfte bei 1 und 5
modulo 6; die Bahn eines Gegenbeispiels ist also auch hier verzerrt.
-/

namespace Collatz

/-- Anzahl der `i < J` mit `x_{i+1} ≡ 5 (mod 6)`. -/
def mod6Cnt (n : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => mod6Cnt n j + (if Titer (j + 1) n % 6 = 5 then 1 else 0)

theorem T_mod4_three {x : Nat} (h : x % 4 = 3) : T x % 6 = 5 := by
  unfold T; rw [if_neg (by omega)]; omega

theorem mod4Cnt_le_mod6Cnt (n : Nat) : ∀ J, mod4Cnt n J ≤ mod6Cnt n J := by
  intro J
  induction J with
  | zero => simp [mod4Cnt, mod6Cnt]
  | succ j ih =>
    simp only [mod4Cnt, mod6Cnt]
    rw [do_Titer_succ]
    by_cases h : Titer j n % 4 = 3
    · rw [if_pos h, if_pos (T_mod4_three h)]; omega
    · rw [if_neg h]; omega

/-- **Satz 68.** Ab dem kleinsten Glied `m ≥ 2^27` eines Gegenbeispiels gilt
`17·J ≤ 65·(#{1 ≤ i ≤ J : x_i ≡ 5 mod 6} + 1)`. -/
theorem orbitMin_mod6 {m : Nat} (hbig : 134217728 ≤ m) (hmin : IsOrbitMin m) (J : Nat) :
    17 * J ≤ 65 * (mod6Cnt m J + 1) := by
  have h := orbitMin_mod4_sharp hbig hmin J
  have := mod4Cnt_le_mod6Cnt m J
  omega

end Collatz
