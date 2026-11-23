import Collatz.OrbitDensity27
import Collatz.Korec

/-!
# Die kleinsten Glieder von Gegenbeispielen bilden eine 2-adische Nullmenge

Satz 36 sagt: Gäbe es ein Gegenbeispiel, dann in **jeder** Restklasse modulo `2^k`. Für das
**kleinste Glied** `m` eines Gegenbeispiels gilt das Gegenteil:

* Nach Satz 32 hat `m ≥ 2^27` zu jeder Zeit mindestens 63 % ungerade Schritte, insbesondere
  `oddsT (1000w) m ≥ 630w` für jedes `w` (`counterexample_min_classes`). Weil `oddsT` nur vom
  Rest abhängt (Terras), liegt `m mod 2^(1000w)` in einer der `minClasses w` Klassen.
* Mit der Chernoff-Zählung aus Satz 33 (`p = 630`, `q = 370`) sind das höchstens ein Anteil
  `2^(−49w)` aller Klassen (`minClasses_small`), weil `2^49 · 1000^1000 ≤ 2^1000 · 630^630 · 370^370`.

Also: Die möglichen Minima bilden 2-adisch eine Nullmenge. Das schliesst aber keine einzelne Zahl
aus, denn auch eine Nullmenge kann natürliche Zahlen enthalten (etwa alle `n` mit lauter
ungeraden Anfangsschritten wie `2^j − 1`).
-/

namespace Collatz

set_option exponentiation.threshold 2000

/-- `oddsT k n` hängt nur von `n mod 2^k` ab. -/
theorem oddsT_mod_two_pow (k n : Nat) : oddsT k (n % 2 ^ k) = oddsT k n := by
  have := oddsT_add k (n % 2 ^ k) (n / 2 ^ k)
  rw [Nat.mod_add_div] at this
  exact this.symm

/-- Die Klassen modulo `2^(1000w)`, in denen das kleinste Glied eines Gegenbeispiels liegen
könnte: mindestens `630w` ungerade unter den ersten `1000w` Schritten. -/
def minClasses (w : Nat) : Nat :=
  countBelow (fun r => decide (630 * w ≤ oddsT (1000 * w) r)) (2 ^ (1000 * w))

theorem minClasses_const : 2 ^ 49 * 1000 ^ 1000 ≤ 2 ^ 1000 * (630 ^ 630 * 370 ^ 370) := by
  decide +kernel

/-- **Zählung.** Höchstens ein Anteil `2^(−49w)` aller Klassen modulo `2^(1000w)`. -/
theorem minClasses_small (w : Nat) : minClasses w * 2 ^ (49 * w) ≤ 2 ^ (1000 * w) := by
  have hc := count_odds_ge (p := 630) (q := 370) (by decide) (1000 * w) (630 * w)
  rw [show 1000 * w - 630 * w = 370 * w by omega, show (630 + 370 : Nat) = 1000 from rfl] at hc
  have e1 : 630 ^ (630 * w) * 370 ^ (370 * w) = (630 ^ 630 * 370 ^ 370) ^ w := by
    rw [Nat.mul_pow, Nat.pow_mul, Nat.pow_mul]
  rw [e1, Nat.pow_mul 1000 1000 w] at hc
  have hk := Nat.pow_le_pow_left minClasses_const w
  rw [Nat.mul_pow, Nat.mul_pow] at hk
  generalize (630 ^ 630 * 370 ^ 370) ^ w = A at hc hk
  generalize hC : minClasses w = C
  rw [show countBelow (fun r => decide (630 * w ≤ oddsT (1000 * w) r)) (2 ^ (1000 * w)) = C
    from hC] at hc
  have hA : 0 < A := by
    apply Nat.pos_of_ne_zero; intro h0; rw [h0, Nat.mul_zero] at hk
    have : 0 < (2 ^ 49) ^ w * (1000 ^ 1000) ^ w := Nat.mul_pos (Nat.pow_pos (by decide))
      (Nat.pow_pos (by decide))
    omega
  apply Nat.le_of_mul_le_mul_right _ hA
  rw [Nat.pow_mul 2 49 w, Nat.pow_mul 2 1000 w]
  calc C * (2 ^ 49) ^ w * A = C * A * (2 ^ 49) ^ w := Nat.mul_right_comm _ _ _
    _ ≤ (1000 ^ 1000) ^ w * (2 ^ 49) ^ w := Nat.mul_le_mul_right _ hc
    _ = (2 ^ 49) ^ w * (1000 ^ 1000) ^ w := Nat.mul_comm _ _
    _ ≤ (2 ^ 1000) ^ w * A := hk

/-- **Satz.** Das kleinste Glied `m` eines Gegenbeispiels liegt für **jedes** `w` modulo
`2^(1000w)` in einer der `minClasses w` Klassen, also in höchstens einem Anteil `2^(−49w)`. -/
theorem counterexample_min_classes {n : Nat} (h0 : 0 < n) (h : ¬ ReachesOne n) :
    ∃ k, IsOrbitMin (iter k n) ∧ 134217728 ≤ iter k n ∧
      ∀ w, 630 * w ≤ oddsT (1000 * w) (iter k n % 2 ^ (1000 * w)) := by
  obtain ⟨k, hbig, hmin, hall, _, _⟩ := counterexample_odd_density h0 h
  refine ⟨k, hmin, hbig, fun w => ?_⟩
  rw [oddsT_mod_two_pow]
  cases w with
  | zero => omega
  | succ v =>
    have hb : (3 * 134217728 + 1) ^ (630 * (v + 1)) <
        2 ^ (1000 * (v + 1)) * 134217728 ^ (630 * (v + 1)) := by
      have := Nat.pow_lt_pow_left bound_1000 (n := v + 1) (by omega)
      rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_mul] at this
      exact this
    exact Nat.le_of_lt (odds_gt_of_bound (by decide) (hall (1000 * (v + 1))) hb)

end Collatz
