import Collatz.OneCycle
import Collatz.Mixing

/-!
# Satz 70: Die Gleichung eines Zyklus mit zwei Aufstiegsblöcken

Ein **2-Zyklus** (im Sinn von Steiner/Simons) hat den Paritätsvektor
`1^a 0^b 1^c 0^d`: `a` ungerade Schritte, `b` gerade, `c` ungerade, `d` gerade, insgesamt
`L = a+b+c+d` Schritte mit `o = a+c` ungeraden. Hier wird die exakte Zyklusgleichung bewiesen:

  `n · (2^L − 3^(a+c)) = 3^c · (3^a − 2^a) + 2^(a+b) · (3^c − 2^c)`.

Daraus folgt sofort `3^(a+c) < 2^L` und, zusammen mit Satz 13 (alle Glieder eines weiteren Zyklus sind
`≥ 2^22`), dass `2^L` extrem nahe bei `3^(a+c)` liegen muss.

Ehrliche Einordnung: Simons (2005) hat 2-Zyklen ganz ausgeschlossen, mit der Theorie der
Linearformen in Logarithmen (Baker). Diese Tiefe steht uns in Lean ohne Mathlib nicht zur
Verfügung; die Gleichung ist der elementare Teil dieses Arguments.
-/

namespace Collatz

theorem tb_split {a b c d n : Nat}
    (hv : parVec (a + b + (c + d)) n =
      (List.replicate a true ++ List.replicate b false) ++
      (List.replicate c true ++ List.replicate d false)) :
    parVec (a + b) n = List.replicate a true ++ List.replicate b false ∧
    parVec (c + d) (Titer (a + b) n) = List.replicate c true ++ List.replicate d false := by
  rw [parVec_add] at hv
  have hl : (parVec (a + b) n).length =
      (List.replicate a true ++ List.replicate b false).length := by
    simp [parVec_length]
  exact List.append_inj hv hl

/-- **Satz 70 (Zwei-Block-Zyklusgleichung).** -/
theorem two_block_cycle_equation {a b c d n : Nat}
    (hc : Titer (a + b + (c + d)) n = n)
    (hv : parVec (a + b + (c + d)) n =
      (List.replicate a true ++ List.replicate b false) ++
      (List.replicate c true ++ List.replicate d false)) :
    2 ^ (a + b + (c + d)) * n
      = 3 ^ (a + c) * n + (3 ^ c * (3 ^ a - 2 ^ a) + 2 ^ (a + b) * (3 ^ c - 2 ^ c)) := by
  obtain ⟨h1, h2⟩ := tb_split hv
  obtain ⟨c1, o1⟩ := parVec_ones_zeros a b n h1
  obtain ⟨c2, o2⟩ := parVec_ones_zeros c d _ h2
  have f1 := Titer_formula (a + b) n
  have f2 := Titer_formula (c + d) (Titer (a + b) n)
  rw [c1, o1] at f1
  rw [c2, o2, ← Titer_add, hc] at f2
  -- 2^(a+b+(c+d)) n = 2^(a+b) · 2^(c+d) n = 2^(a+b) (3^c x + C2)
  rw [Nat.pow_add 2 (a + b) (c + d), Nat.mul_assoc, f2, Nat.mul_add,
    Nat.mul_left_comm (2 ^ (a + b)) (3 ^ c), f1, Nat.mul_add, Nat.pow_add 3 a c]
  generalize 3 ^ c * (3 ^ a - 2 ^ a) = A
  generalize 2 ^ (a + b) * (3 ^ c - 2 ^ c) = B
  rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ c) (3 ^ a)]
  omega

/-- Folgerung: Ein solcher Zyklus (mit `a ≥ 1`) braucht `3^(a+c) < 2^L`, und
`n · (2^L − 3^(a+c))` ist genau die rechte Seite. -/
theorem two_block_cycle_gap {a b c d n : Nat} (ha : 0 < a)
    (hc : Titer (a + b + (c + d)) n = n)
    (hv : parVec (a + b + (c + d)) n =
      (List.replicate a true ++ List.replicate b false) ++
      (List.replicate c true ++ List.replicate d false)) :
    3 ^ (a + c) < 2 ^ (a + b + (c + d)) ∧
    n * (2 ^ (a + b + (c + d)) - 3 ^ (a + c))
      = 3 ^ c * (3 ^ a - 2 ^ a) + 2 ^ (a + b) * (3 ^ c - 2 ^ c) := by
  have he := two_block_cycle_equation hc hv
  have hpos : 0 < 3 ^ c * (3 ^ a - 2 ^ a) := by
    have : 2 ^ a < 3 ^ a := Nat.pow_lt_pow_left (by omega) (by omega)
    exact Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
  generalize 3 ^ c * (3 ^ a - 2 ^ a) = A at he hpos ⊢
  generalize 2 ^ (a + b) * (3 ^ c - 2 ^ c) = B at he ⊢
  generalize 2 ^ (a + b + (c + d)) = P at he ⊢
  generalize 3 ^ (a + c) = Q at he ⊢
  have hlt : Q * n < P * n := by rw [Nat.mul_comm P, Nat.mul_comm Q] at *; omega
  have hQP : Q < P := Nat.lt_of_mul_lt_mul_right hlt
  refine ⟨hQP, ?_⟩
  rw [Nat.mul_sub, Nat.mul_comm n P, Nat.mul_comm n Q]
  omega

end Collatz
