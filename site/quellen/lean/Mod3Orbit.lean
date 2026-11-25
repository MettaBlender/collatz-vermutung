import Collatz.Mod4Sharp

/-!
# Satz 67: Die Bahn eines Gegenbeispiels liegt überwiegend bei Rest 2 modulo 3

Für die beschleunigte Abbildung gilt: Nach jedem ungeraden Schritt ist `(3x+1)/2 ≡ 2 (mod 3)`,
denn `3x+1 ≡ 1` und `2·2 ≡ 1 (mod 3)`. Ein gerader Schritt `x ↦ x/2` vertauscht nur die Reste
`1` und `2` (und erhält `0`). Die Reste modulo 3 entlang der Bahn sind also vollständig durch die
Paritätsfolge bestimmt.

Daraus folgt rein kombinatorisch: Unter `x_1, …, x_J` liegen mindestens so viele Glieder bei
Rest 2 wie es ungerade Schritte unter den ersten `J` gibt. Zusammen mit der Dichteschranke heisst
das: Ab dem kleinsten Glied `m ≥ 2^27` eines Gegenbeispiels liegen mehr als `41/65 ≈ 63 %`
der Bahnglieder bei Rest 2 modulo 3, und höchstens `24/65 ≈ 37 %` bei Rest 1.
-/

namespace Collatz

theorem T_odd_mod3 {x : Nat} (h : x % 2 = 1) : T x % 3 = 2 := by
  unfold T; rw [if_neg (by omega)]; omega

/-- Anzahl der `i < J` mit `x_{i+1} ≡ r (mod 3)`. -/
def mod3Cnt (r n : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => mod3Cnt r n j + (if Titer (j + 1) n % 3 = r then 1 else 0)

/-- Jeder ungerade Schritt landet bei Rest 2: `#ungerade ≤ #{Rest 2}`. -/
theorem odds_le_mod3_two (n : Nat) : ∀ J, oddsT J n ≤ mod3Cnt 2 n J := by
  intro J
  induction J with
  | zero => simp [oddsT, mod3Cnt]
  | succ j ih =>
    rw [oddsT_succ]
    simp only [mod3Cnt]
    rw [do_Titer_succ]
    by_cases h : Titer j n % 2 = 1
    · rw [if_pos h, if_pos (T_odd_mod3 h)]; omega
    · rw [if_neg h]; omega

theorem mod3_one_two_le (n : Nat) : ∀ J, mod3Cnt 1 n J + mod3Cnt 2 n J ≤ J := by
  intro J
  induction J with
  | zero => simp [mod3Cnt]
  | succ j ih =>
    simp only [mod3Cnt]
    split <;> split <;> omega

/-- Höchstens so viele Glieder bei Rest 1 wie gerade Schritte. -/
theorem mod3_one_le_evens (n J : Nat) : mod3Cnt 1 n J + oddsT J n ≤ J := by
  have := odds_le_mod3_two n J
  have := mod3_one_two_le n J
  omega

/-- **Satz 67.** Ab dem kleinsten Glied `m ≥ 2^27` eines Gegenbeispiels liegen unter
`x_1, …, x_J` mindestens `41/65·J` Glieder bei Rest 2 modulo 3 und höchstens `24/65·J`
bei Rest 1. -/
theorem orbitMin_mod3 {m : Nat} (hbig : 134217728 ≤ m) (hmin : IsOrbitMin m) (J : Nat) :
    41 * J ≤ 65 * mod3Cnt 2 m J ∧ 65 * mod3Cnt 1 m J ≤ 24 * J := by
  have hd := orbitMin_density (by omega) hmin J
  have hr := ms_ratio (by omega) hd (ms_mono (by decide) hbig ms_const)
  have h2 := odds_le_mod3_two m J
  have h1 := mod3_one_le_evens m J
  omega

end Collatz
