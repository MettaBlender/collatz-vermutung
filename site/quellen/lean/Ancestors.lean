import Collatz.KrasikovBound

/-!
# Satz 50: Vorfahren-Dichotomie

Für eine Zahl `n > 0` gibt es zwei völlig verschiedene Fälle:

* `3 ∣ n`: Jeder Vorfahre `m` (also `step^j(m) = n`) ist `m = 2^j · n`. Bis `x` gibt es also nur
  etwa `log₂(x/n)` Vorfahren, und `n` hat keinen ungeraden Vorfahren ausser sich selbst.
* `3 ∤ n`: Für jedes `k` gibt es mindestens `58 525 359 050 790 615^k` verschiedene Vorfahren
  `m` mit `3^(50k)·m ≤ 6n·2^(163k)`, also etwa `(x/n)^0.665` Vorfahren bis `x`.

Der zweite Teil verallgemeinert Satz 47 (dort war `n = 1` bzw. die Wurzel `5`) auf **jede** nicht
durch 3 teilbare Zahl: Ein ungerader Vorfahre `c = (2^E n − 1)/3` mit `E ≤ 4` und `3 ∤ c`
existiert immer, und unter `c` liefert der Block-Satz die Knoten.
-/

namespace Collatz

/-- Vorfahren von Vielfachen von 3 sind nur Verdopplungen. -/
theorem ancestors_of_three_mul {n : Nat} (h3 : n % 3 = 0) :
    ∀ j m, iter j m = n → m = 2 ^ j * n := by
  intro j
  induction j with
  | zero => intro m h; simpa using h
  | succ j ih =>
    intro m h
    rw [iter_succ] at h
    have hs := ih (step m) h
    unfold step at hs
    split at hs
    · rw [Nat.pow_succ]
      have : m = 2 * (m / 2) := by omega
      rw [this, hs]; ac_rfl
    · exfalso
      have : (2 ^ j * n) % 3 = 0 := by
        rw [Nat.mul_mod, h3, Nat.mul_zero, Nat.zero_mod]
      omega

theorem iter_two_pow_mul : ∀ E n, iter E (2 ^ E * n) = n := by
  intro E
  induction E with
  | zero => intro n; simp
  | succ E ih =>
    intro n
    rw [iter_succ, step_even (by rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2 n, ← Nat.mul_assoc]; omega)]
    have : 2 ^ (E + 1) * n / 2 = 2 ^ E * n := by
      rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2 n, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide)]
    rw [this, ih]

/-- Ein ungerader, nicht durch 3 teilbarer Vorfahre `c ≤ 6n`. -/
theorem odd_ancestor {n : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) :
    ∃ c i, c % 2 = 1 ∧ c % 3 ≠ 0 ∧ c ≤ 6 * n ∧ iter i c = n := by
  have key : ∀ E, 1 ≤ E → E ≤ 4 → (2 ^ E * n) % 9 = 4 ∨ (2 ^ E * n) % 9 = 7 →
      ∃ c i, c % 2 = 1 ∧ c % 3 ≠ 0 ∧ c ≤ 6 * n ∧ iter i c = n := by
    intro E hE hE4 hm
    have hev : (2 ^ E * n) % 2 = 0 := by
      obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
      rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2, ← Nat.mul_assoc, Nat.mul_mod_left]
    have hle : 2 ^ E * n ≤ 16 * n :=
      Nat.mul_le_mul_right _ (Nat.le_trans (Nat.pow_le_pow_right (by decide) hE4) (by decide))
    generalize hN : 2 ^ E * n = N at hm hev hle
    refine ⟨(N - 1) / 3, 1 + E, by omega, by omega, by omega, ?_⟩
    rw [iter_add]
    have hc : step ((N - 1) / 3) = N := by
      rw [step, if_neg (by omega)]; omega
    show iter E (step ((N - 1) / 3)) = n
    rw [hc, ← hN, iter_two_pow_mul]
  have : n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 7 ∨ n % 9 = 8 := by omega
  rcases this with h | h | h | h | h | h
  · exact key 2 (by decide) (by decide) (by rw [show (2:Nat) ^ 2 = 4 from rfl]; omega)
  · exact key 1 (by decide) (by decide) (by rw [show (2:Nat) ^ 1 = 2 from rfl]; omega)
  · exact key 2 (by decide) (by decide) (by rw [show (2:Nat) ^ 2 = 4 from rfl]; omega)
  · exact key 3 (by decide) (by decide) (by rw [show (2:Nat) ^ 3 = 8 from rfl]; omega)
  · exact key 4 (by decide) (by decide) (by rw [show (2:Nat) ^ 4 = 16 from rfl]; omega)
  · exact key 1 (by decide) (by decide) (by rw [show (2:Nat) ^ 1 = 2 from rfl]; omega)

/-- **Satz 50.** Jede Zahl `n > 0` mit `3 ∤ n` hat für jedes `k` mindestens
`58 525 359 050 790 615^k` verschiedene Vorfahren `m` mit `3^(50k)·m ≤ 2^(163k)·6n`. -/
theorem krasikov_ancestors {n : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) (k : Nat) :
    ∃ L : List Nat, L.Nodup ∧ 58525359050790615 ^ k ≤ L.length ∧
      ∀ m ∈ L, 3 ^ (k * 50) * m ≤ 2 ^ (k * 163) * (6 * n) ∧ ∃ j, iter j m = n := by
  obtain ⟨c, i, hc1, hc3, hcn, hci⟩ := odd_ancestor h0 h3
  obtain ⟨q, hc, hq⟩ := cert50
  obtain ⟨L, hn, hl, hg⟩ := block (by decide) hc (Nat.le_refl 50) (Nat.le_refl 163)
    (fun t ht h3 => by rw [hq]; exact final50 t ht h3) k c hc1 hc3
  refine ⟨L, hn, hl, fun m hm => ⟨?_, ?_⟩⟩
  · exact Nat.le_trans (hg m hm).2.2.1 (Nat.mul_le_mul_left _ hcn)
  · obtain ⟨j, hj⟩ := (hg m hm).2.2.2.2
    exact ⟨j + i, by rw [iter_add, hj, hci]⟩

end Collatz
