import Collatz.DenseTree

/-!
# Gegenbeispiele lägen sogar in jeder Restklasse modulo `3 · 2^k`

Verfeinerung von Satz 36: Ist `n > 0` nicht durch 3 teilbar, so hat `n` in jeder Restklasse
modulo `2^k` Vorfahren mit **jedem** Rest modulo 3 (`ancestor_in_class3`). Insbesondere:
Gäbe es ein Gegenbeispiel, dann gäbe es in jeder Restklasse modulo `2^k` auch ein durch 3
teilbares (`counterexample_mult_three`), obwohl Vielfache von 3 Blätter des Rückwärtsbaums sind.

Idee: In `2^m n = y + 3^o b` darf man `m` durch `m + 2·3^(o−1)` ersetzen (Multiplikation mit
`4^(3^(o−1)) = 1 + 3^o w`, `w ≡ 1 mod 3`). Dabei wächst `b` modulo 3 um `y ≢ 0`, also nimmt
`b` und damit der Vorfahre `s + 2^k b` jeden Rest modulo 3 an. Hat der Rest `s` keinen
ungeraden Schritt, geht man zu einer der beiden Verfeinerungen modulo `2^(k+1)` über.
-/

namespace Collatz

theorem bump3 {j m n y b : Nat} (h : 2 ^ m * n = y + 3 ^ (j + 1) * b) :
    ∃ b', 2 ^ (m + 2 * 3 ^ j) * n = y + 3 ^ (j + 1) * b' ∧ b' % 3 = (b + y) % 3 := by
  obtain ⟨w, hw, hP⟩ := four_lift j
  generalize hM : 3 ^ (j + 1) = M at h hP
  have hM3 : M % 3 = 0 := by rw [← hM, Nat.pow_succ]; exact Nat.mul_mod_left _ 3
  refine ⟨b + y * w + M * (b * w), ?_, ?_⟩
  · have e : 2 ^ (m + 2 * 3 ^ j) * n = 2 ^ m * n * 4 ^ (3 ^ j) := by
      rw [Nat.pow_add, Nat.pow_mul, show (2 : Nat) ^ 2 = 4 from rfl, Nat.mul_right_comm]
    rw [e, h, hP]
    grind
  · have h1 : (y * w) % 3 = y % 3 := by rw [Nat.mul_mod, hw, Nat.mul_one, Nat.mod_mod]
    have h2 : (M * (b * w)) % 3 = 0 := by rw [Nat.mul_mod, hM3, Nat.zero_mul, Nat.zero_mod]
    omega

/-- Mit mindestens einem ungeraden Schritt: Vorfahren in der Klasse `s` mit jedem Rest mod 3. -/
theorem hit_class3 {n K s : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) (hs : s < 2 ^ K)
    (ho : 1 ≤ oddsT K s) (t : Nat) :
    ∃ x j, x % 2 ^ K = s ∧ x % 3 = t % 3 ∧ Titer j x = n := by
  have hy := Titer_mod_three K s ho
  obtain ⟨j, hj⟩ : ∃ j, oddsT K s = j + 1 := ⟨oddsT K s - 1, by omega⟩
  generalize hY : Titer K s = y at hy
  obtain ⟨m, b0, h0'⟩ := two_pow_hits (j + 1) n y h3 hy h0
  obtain ⟨b1, h1, e1⟩ := bump3 h0'
  obtain ⟨b2, h2, e2⟩ := bump3 h1
  -- jeder Kandidat x = s + 2^K b ist ein Vorfahre
  have cand : ∀ m b, 2 ^ m * n = y + 3 ^ (j + 1) * b →
      (s + 2 ^ K * b) % 2 ^ K = s ∧ Titer (K + m) (s + 2 ^ K * b) = n := by
    intro m b h
    refine ⟨by rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hs, ?_⟩
    rw [Titer_add, (affine K s b).1, hY, hj, ← h, Titer_two_pow]
  -- 2^K ≡ u (mod 3) mit u ∈ {1, 2}
  have hu : 2 ^ K % 3 = 1 ∨ 2 ^ K % 3 = 2 := by
    have : 2 ^ K % 3 ≠ 0 := by
      intro hz
      have := Nat.Coprime.pow_left K (show Nat.Coprime 2 3 by decide)
      have hd : 3 ∣ 2 ^ K := Nat.dvd_of_mod_eq_zero hz
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm this) hd
      omega
    omega
  obtain ⟨q, u, hq, hu'⟩ : ∃ q u, 2 ^ K = 3 * q + u ∧ (u = 1 ∨ u = 2) :=
    ⟨2 ^ K / 3, 2 ^ K % 3, by omega, hu⟩
  have ex : ∀ b, (s + 2 ^ K * b) % 3 = (s + u * b) % 3 := by
    intro b; rw [hq, Nat.add_mul]
    have : 3 * q * b = 3 * (q * b) := Nat.mul_assoc 3 q b
    omega
  have hb1 : b1 % 3 = (b0 + y) % 3 := e1
  have hb2 : b2 % 3 = (b1 + y) % 3 := e2
  have pick : (s + u * b0) % 3 = t % 3 ∨ (s + u * b1) % 3 = t % 3 ∨ (s + u * b2) % 3 = t % 3 := by
    have hyy : y % 3 = 1 ∨ y % 3 = 2 := by omega
    rcases hu' with rfl | rfl <;> rcases hyy with hyy | hyy <;> omega
  rcases pick with p | p | p
  · obtain ⟨a, c⟩ := cand m b0 h0'; exact ⟨_, _, a, by rw [ex]; exact p, c⟩
  · obtain ⟨a, c⟩ := cand _ b1 h1; exact ⟨_, _, a, by rw [ex]; exact p, c⟩
  · obtain ⟨a, c⟩ := cand _ b2 h2; exact ⟨_, _, a, by rw [ex]; exact p, c⟩

/-- **Satz.** Vorfahren in jeder Klasse modulo `2^k` mit jedem Rest modulo 3. -/
theorem ancestor_in_class3 {n : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) (k s t : Nat) :
    ∃ x i, x % 2 ^ k = s % 2 ^ k ∧ x % 3 = t % 3 ∧ iter i x = n := by
  suffices hT : ∃ x j, x % 2 ^ k = s % 2 ^ k ∧ x % 3 = t % 3 ∧ Titer j x = n by
    obtain ⟨x, j, a, b, c⟩ := hT
    exact ⟨x, j + oddsT j x, a, b, by rw [← Titer_eq_iter]; exact c⟩
  generalize hs' : s % 2 ^ k = s'
  have hlt : s' < 2 ^ k := by rw [← hs']; exact Nat.mod_lt _ (Nat.two_pow_pos k)
  by_cases ho : 1 ≤ oddsT k s'
  · exact hit_class3 h0 h3 hlt ho t
  · -- verfeinern: s'' = s' oder s' + 2^k, je nachdem welches T^k(·) ungerade macht
    have ho0 : oddsT k s' = 0 := by omega
    have hdv : 2 ^ k ∣ 2 ^ (k + 1) := Nat.pow_dvd_pow 2 (by omega)
    have hk1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have fin : ∀ s'', s'' < 2 ^ (k + 1) → s'' % 2 ^ k = s' → 1 ≤ oddsT (k + 1) s'' →
        ∃ x j, x % 2 ^ k = s' ∧ x % 3 = t % 3 ∧ Titer j x = n := by
      intro s'' h1 h2 h3'
      obtain ⟨x, j, a, b, c⟩ := hit_class3 h0 h3 h1 h3' t
      refine ⟨x, j, ?_, b, c⟩
      rw [← Nat.mod_mod_of_dvd x hdv, a, h2]
    by_cases hp : Titer k s' % 2 = 1
    · refine fin s' (by omega) (Nat.mod_eq_of_lt hlt) ?_
      rw [oddsT_succ, if_pos hp]; omega
    · have haff := (affine k s' 1).1
      rw [ho0, Nat.pow_zero, Nat.mul_one, Nat.mul_one] at haff
      refine fin (s' + 2 ^ k) (by omega) ?_ ?_
      · rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt hlt
      · rw [oddsT_succ, if_pos (by rw [haff]; omega)]; omega

/-- **Gäbe es ein Gegenbeispiel, dann in jeder Klasse modulo `2^k` auch ein durch 3 teilbares.** -/
theorem counterexample_mult_three (h : ¬ CollatzConjecture) (k s t : Nat) :
    ∃ m, 0 < m ∧ m % 2 ^ k = s % 2 ^ k ∧ m % 3 = t % 3 ∧ ¬ ReachesOne m := by
  obtain ⟨n, hn, hr⟩ : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact h (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  obtain ⟨n', hn', h3, hr'⟩ := counterexample_not_three n hn hr
  obtain ⟨m, i, hm, hm3, hi⟩ := ancestor_in_class3 hn' h3 k s t
  refine ⟨m, ?_, hm, hm3, fun hm1 => hr' (hi ▸ reachesOne_iter hm1 i)⟩
  apply Nat.pos_of_ne_zero
  intro hz
  have : iter i 0 = 0 := by
    clear hi; induction i with
    | zero => rfl
    | succ i ih => rw [iter_succ, show step 0 = 0 from rfl, ih]
  rw [← hz] at this; omega

end Collatz
