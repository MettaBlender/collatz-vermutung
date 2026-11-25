import Collatz.DoubleOddDensity

/-!
# Satz 65: Doppel-Aufstieg heisst Rest 3 modulo 4

Ein Doppel-Aufstieg an der Stelle `i` (zwei ungerade Schritte hintereinander) liegt genau
dann vor, wenn `x_i ≡ 3 (mod 4)`. Damit wird Satz 64 zu einer Aussage über Restklassen:
Ab dem kleinsten Glied eines Gegenbeispiels liegt unter den ersten `J` Bahngliedern an
mindestens `J/4 - 1` Stellen der Rest 3 modulo 4.
-/

namespace Collatz

theorem double_odd_iff_mod4 (i n : Nat) :
    (nthPar i n = true ∧ nthPar (i + 1) n = true) ↔ Titer i n % 4 = 3 := by
  unfold nthPar
  rw [do_Titer_succ]
  unfold T
  generalize Titer i n = x
  constructor
  · intro ⟨h1, h2⟩
    simp at h1 h2
    rw [if_neg (by omega)] at h2
    omega
  · intro h
    have hx : ¬ x % 2 = 0 := by omega
    rw [if_neg hx]
    simp
    omega

/-- Anzahl der `i < J` mit `x_i ≡ 3 (mod 4)`. -/
def mod4Cnt (n : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => mod4Cnt n j + (if Titer j n % 4 = 3 then 1 else 0)

theorem doCnt_eq_mod4Cnt (n : Nat) : ∀ J, doCnt n 0 J = mod4Cnt n J := by
  intro J
  induction J with
  | zero => rfl
  | succ j ih =>
    simp only [doCnt, mod4Cnt, ih]
    have h := double_odd_iff_mod4 j n
    rw [show 0 + j = j by omega]
    by_cases hc : Titer j n % 4 = 3
    · rw [if_pos (h.mpr hc), if_pos hc]
    · rw [if_neg (fun hp => hc (h.mp hp)), if_neg hc]

/-- **Satz 65.** Ab dem kleinsten Glied `m ≥ 2^27` eines Gegenbeispiels gilt
`J ≤ 4·(#{i < J : x_i ≡ 3 mod 4} + 1)`. -/
theorem orbitMin_mod4_density {m : Nat} (hbig : 134217728 ≤ m) (hmin : IsOrbitMin m)
    (J : Nat) : J ≤ 4 * (mod4Cnt m J + 1) := by
  rw [← doCnt_eq_mod4Cnt]
  exact orbitMin_double_odd_density hbig hmin J

end Collatz
