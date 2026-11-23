import Collatz.OrbitDensity
import Collatz.Verified27All

/-!
# Steckbrief eines Gegenbeispiels: mindestens 63.09 % ungerade Schritte, zu jeder Zeit

Das kleinste Glied `m` eines Gegenbeispiels ist `≥ 2^27` (Satz 27) und fällt nie unter sich.
Mit `orbitMin_density` und `density_mono` gilt für **jedes** `k`:
`2^k · (2^27)^o ≤ (3·2^27 + 1)^o`. Konkret: unter den ersten 1000 Schritten von `T` mindestens
631 ungerade, unter den ersten 10 000 mindestens 6310.
-/

namespace Collatz

theorem bound_1000 : (3 * 134217728 + 1) ^ 630 < 2 ^ 1000 * 134217728 ^ 630 := by decide +kernel
theorem bound_10000 : (3 * 134217728 + 1) ^ 6309 < 2 ^ 10000 * 134217728 ^ 6309 := by decide +kernel

/-- **Ein Gegenbeispiel hat zu jeder Zeit mindestens etwa 63.09 % ungerade Schritte.** -/
theorem counterexample_odd_density {n : Nat} (h0 : 0 < n) (h : ¬ ReachesOne n) :
    ∃ k, 134217728 ≤ iter k n ∧ IsOrbitMin (iter k n) ∧
      (∀ j, 2 ^ j * 134217728 ^ oddsT j (iter k n) ≤ (3 * 134217728 + 1) ^ oddsT j (iter k n)) ∧
      631 ≤ oddsT 1000 (iter k n) ∧ 6310 ≤ oddsT 10000 (iter k n) := by
  obtain ⟨k, hbig, hmin, _⟩ := counterexample_structure27 h0 h
  have hall : ∀ j, 2 ^ j * 134217728 ^ oddsT j (iter k n) ≤
      (3 * 134217728 + 1) ^ oddsT j (iter k n) :=
    fun j => density_mono (by decide) hbig (orbitMin_density (by omega) hmin j)
  exact ⟨k, hbig, hmin, hall, odds_gt_of_bound (by decide) (hall 1000) bound_1000,
    odds_gt_of_bound (by decide) (hall 10000) bound_10000⟩

end Collatz
