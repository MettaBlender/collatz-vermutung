import Collatz.DenseTree

/-!
# Gegenbeispiele wären auch 3-adisch dicht

Satz 36 zeigt: Gegenbeispiele lägen in jeder Restklasse modulo `2^k` (2-adisch dicht). Hier das
Gegenstück für die **andere** Primzahl der Abbildung `3n + 1`:

* `ancestor_mod_three_pow`: Ist `n > 0` nicht durch 3 teilbar, so hat `n` in **jeder** Restklasse
  modulo `3^j` einen ungeraden Vorfahren `a` mit `3a + 1 = 2^e · n`.
* **Satz** (`counterexample_mod_three_pow`): Gäbe es ein Gegenbeispiel, dann gäbe es eines in
  **jeder** Restklasse modulo `3^j`, für alle `j`.
* `infinitely_many_in_class6` (Satz 44): Dann sogar unendlich viele in jeder Klasse modulo
  `2^k · 3^J`.
* `conjecture_iff_class3`: Die Vermutung ist äquivalent zu ihr für eine einzige Restklasse
  modulo `3^j`.

Beweis in einer Zeile: Da 2 Primitivwurzel modulo `3^(j+1)` ist (`two_pow_hits`), gibt es `e ≥ 1`
mit `2^e · n ≡ 3t + 1 (mod 3^(j+1))`. Dann ist `a = (2^e n − 1)/3 ≡ t (mod 3^j)`, und `a` ist
ungerade, weil `3a + 1 = 2^e n` gerade ist.

Bedeutung: Auch 3-adische Argumente (Restklassen modulo `3^j`) können ein Gegenbeispiel nie
ausschliessen. Zusammen mit Satz 35 und 36: Ein Beweis darf weder nur 2-adisch noch nur
3-adisch argumentieren, er muss die Grösse von `n` benutzen.
-/

namespace Collatz

/-- **Vorfahren in jeder Klasse modulo `3^j`.** -/
theorem ancestor_mod_three_pow {n : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) (j t : Nat) :
    ∃ a e, a % 3 ^ j = t % 3 ^ j ∧ a % 2 = 1 ∧ 3 * a + 1 = 2 ^ (e + 1) * n ∧
      iter (e + 2) a = n := by
  have h2n : (2 * n) % 3 ≠ 0 := by omega
  obtain ⟨m, b, hb⟩ := two_pow_hits (j + 1) (2 * n) (3 * (t % 3 ^ j) + 1) h2n (by omega)
    (by omega)
  have hmn : 2 ^ m * (2 * n) = 2 ^ (m + 1) * n := by rw [Nat.pow_succ]; grind
  rw [hmn] at hb
  refine ⟨t % 3 ^ j + 3 ^ j * b, m, ?_, ?_, ?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
  · have he : (2 ^ (m + 1) * n) % 2 = 0 := by
      rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_assoc, Nat.mul_mod_right]
    have : 3 * (t % 3 ^ j + 3 ^ j * b) + 1 = 2 ^ (m + 1) * n := by
      rw [hb, Nat.pow_succ]; grind
    omega
  · rw [hb, Nat.pow_succ]; grind
  · have h3a : 3 * (t % 3 ^ j + 3 ^ j * b) + 1 = 2 ^ (m + 1) * n := by
      rw [hb, Nat.pow_succ]; grind
    have hodd : (t % 3 ^ j + 3 ^ j * b) % 2 = 1 := by
      have he : (2 ^ (m + 1) * n) % 2 = 0 := by
        rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_assoc, Nat.mul_mod_right]
      omega
    rw [show m + 2 = 1 + (m + 1) by omega, iter_add]
    show iter (m + 1) (step (t % 3 ^ j + 3 ^ j * b)) = n
    rw [step_odd hodd, h3a, iter_double_pow]

/-- **Satz.** Gäbe es ein Gegenbeispiel, dann gäbe es eines in jeder Restklasse modulo `3^j`. -/
theorem counterexample_mod_three_pow (h : ¬ CollatzConjecture) (j t : Nat) :
    ∃ a, 0 < a ∧ a % 3 ^ j = t % 3 ^ j ∧ ¬ ReachesOne a := by
  have : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact h (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  obtain ⟨n, hn, hr⟩ := this
  obtain ⟨n', hn', h3, hr'⟩ := counterexample_not_three n hn hr
  obtain ⟨a, e, ha, hodd, -, hi⟩ := ancestor_mod_three_pow hn' h3 j t
  exact ⟨a, by omega, ha, fun ha1 => hr' (hi ▸ reachesOne_iter ha1 (e + 2))⟩

/-- **Eine Klasse modulo `3^j` genügt.** -/
theorem conjecture_iff_class3 (j t : Nat) :
    CollatzConjecture ↔ ∀ a, 0 < a → a % 3 ^ j = t % 3 ^ j → ReachesOne a := by
  constructor
  · intro h a ha _; exact h a ha
  · intro h
    apply Classical.byContradiction
    intro hc
    obtain ⟨a, ha, hs, hr⟩ := counterexample_mod_three_pow hc j t
    exact hr (h a ha hs)

/-- `2^K` ist modulo 3 nie 0. -/
theorem two_pow_mod_three (K : Nat) : 2 ^ K % 3 ≠ 0 := by
  induction K with
  | zero => decide
  | succ K ih => rw [Nat.pow_succ]; omega

/-- Lineare Kongruenz: Es gibt `b₀` mit `s + 2^K·b₀ ≡ t (mod 3^J)` (2 ist modulo `3^J` invertierbar). -/
theorem solve_lin (J K s t : Nat) : ∃ b0, (s + 2 ^ K * b0) % 3 ^ J = t % 3 ^ J := by
  obtain ⟨m, c, hc⟩ := two_pow_hits J (2 ^ K) 1 (two_pow_mod_three K) (by decide)
    (Nat.two_pow_pos K)
  have hs : s ≤ 3 ^ J * s := Nat.le_mul_of_pos_left s (Nat.pow_pos (by decide))
  refine ⟨2 ^ m * (t + (3 ^ J * s - s)), ?_⟩
  have e : s + 2 ^ K * (2 ^ m * (t + (3 ^ J * s - s))) =
      t + 3 ^ J * (s + c * (t + (3 ^ J * s - s))) := by
    have : 2 ^ K * (2 ^ m * (t + (3 ^ J * s - s))) = (2 ^ m * 2 ^ K) * (t + (3 ^ J * s - s)) := by
      grind
    rw [this, hc]
    generalize hD : 3 ^ J * s - s = D
    have hD' : 3 ^ J * s = s + D := by omega
    grind
  rw [e, Nat.add_mul_mod_self_left]

/-- Mit mindestens einem ungeraden Schritt: Vorfahren in der Klasse `s` mod `2^K` und jeder
Klasse `t` mod `3^J`. -/
theorem hit_class6 {n K s : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) (hs : s < 2 ^ K)
    (ho : 1 ≤ oddsT K s) (J t : Nat) :
    ∃ x j, x % 2 ^ K = s ∧ x % 3 ^ J = t % 3 ^ J ∧ Titer j x = n := by
  have hy := Titer_mod_three K s ho
  obtain ⟨o, hj⟩ : ∃ o, oddsT K s = o + 1 := ⟨oddsT K s - 1, by omega⟩
  generalize hY : Titer K s = y at hy
  obtain ⟨b0, hb0⟩ := solve_lin J K s t
  have hy' : (y + 3 ^ (o + 1) * b0) % 3 ≠ 0 := by
    have e : y + 3 ^ (o + 1) * b0 = y + 3 * (3 ^ o * b0) := by rw [Nat.pow_succ]; grind
    rw [e, Nat.add_mul_mod_self_left]; exact hy
  obtain ⟨m, c, hc⟩ := two_pow_hits (o + 1 + J) n (y + 3 ^ (o + 1) * b0) h3 hy' h0
  have hc' : 2 ^ m * n = y + 3 ^ (o + 1) * (b0 + 3 ^ J * c) := by
    rw [hc, Nat.pow_add]; grind
  refine ⟨s + 2 ^ K * (b0 + 3 ^ J * c), K + m, ?_, ?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hs
  · have : s + 2 ^ K * (b0 + 3 ^ J * c) = (s + 2 ^ K * b0) + 3 ^ J * (2 ^ K * c) := by grind
    rw [this, Nat.add_mul_mod_self_left, hb0]
  · rw [Titer_add, (affine K s _).1, hY, hj, ← hc', Titer_two_pow]

/-- **Satz.** Ist `n > 0` nicht durch 3 teilbar, so hat `n` Vorfahren in jeder Restklasse
modulo `2^k` **und gleichzeitig** jeder Restklasse modulo `3^J`. -/
theorem ancestor_in_class6 {n : Nat} (h0 : 0 < n) (h3 : n % 3 ≠ 0) (k s J t : Nat) :
    ∃ x i, x % 2 ^ k = s % 2 ^ k ∧ x % 3 ^ J = t % 3 ^ J ∧ iter i x = n := by
  suffices hT : ∃ x j, x % 2 ^ k = s % 2 ^ k ∧ x % 3 ^ J = t % 3 ^ J ∧ Titer j x = n by
    obtain ⟨x, j, a, b, c⟩ := hT
    exact ⟨x, j + oddsT j x, a, b, by rw [← Titer_eq_iter]; exact c⟩
  generalize hs' : s % 2 ^ k = s'
  have hlt : s' < 2 ^ k := by rw [← hs']; exact Nat.mod_lt _ (Nat.two_pow_pos k)
  by_cases ho : 1 ≤ oddsT k s'
  · exact hit_class6 h0 h3 hlt ho J t
  · have ho0 : oddsT k s' = 0 := by omega
    have hdv : 2 ^ k ∣ 2 ^ (k + 1) := Nat.pow_dvd_pow 2 (by omega)
    have hk1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have fin : ∀ s'', s'' < 2 ^ (k + 1) → s'' % 2 ^ k = s' → 1 ≤ oddsT (k + 1) s'' →
        ∃ x j, x % 2 ^ k = s' ∧ x % 3 ^ J = t % 3 ^ J ∧ Titer j x = n := by
      intro s'' h1 h2 h3'
      obtain ⟨x, j, a, b, c⟩ := hit_class6 h0 h3 h1 h3' J t
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

/-- **Satz.** Gäbe es ein Gegenbeispiel, dann gäbe es eines in jeder Restklasse modulo `2^k`
und zugleich jeder Restklasse modulo `3^J` (also in jeder Klasse modulo `2^k · 3^J`). -/
theorem counterexample_in_class6 (h : ¬ CollatzConjecture) (k s J t : Nat) :
    ∃ x, 0 < x ∧ x % 2 ^ k = s % 2 ^ k ∧ x % 3 ^ J = t % 3 ^ J ∧ ¬ ReachesOne x := by
  have : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact h (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  obtain ⟨n, hn, hr⟩ := this
  obtain ⟨n', hn', h3, hr'⟩ := counterexample_not_three n hn hr
  obtain ⟨x, i, hx2, hx3, hi⟩ := ancestor_in_class6 hn' h3 k s J t
  refine ⟨x, ?_, hx2, hx3, fun hx1 => hr' (hi ▸ reachesOne_iter hx1 i)⟩
  apply Nat.pos_of_ne_zero
  intro hz
  have : iter i 0 = 0 := by
    clear hi; induction i with
    | zero => rfl
    | succ i ih => rw [iter_succ, show step 0 = 0 from rfl, ih]
  rw [← hz] at this; omega

/-- **Eine Klasse modulo `2^k · 3^J` genügt.** -/
theorem conjecture_iff_class6 (k s J t : Nat) :
    CollatzConjecture ↔
      ∀ x, 0 < x → x % 2 ^ k = s % 2 ^ k → x % 3 ^ J = t % 3 ^ J → ReachesOne x := by
  constructor
  · intro h x hx _ _; exact h x hx
  · intro h
    apply Classical.byContradiction
    intro hc
    obtain ⟨x, hx, h2, h3, hr⟩ := counterexample_in_class6 hc k s J t
    exact hr (h x hx h2 h3)

/-- **Satz.** Gäbe es ein Gegenbeispiel, dann gäbe es in jeder Restklasse modulo `2^k · 3^J`
**unendlich viele**: über jeder Schranke `N` noch eines. -/
theorem infinitely_many_in_class6 (h : ¬ CollatzConjecture) (k s J t N : Nat) :
    ∃ x, N < x ∧ x % 2 ^ k = s % 2 ^ k ∧ x % 3 ^ J = t % 3 ^ J ∧ ¬ ReachesOne x := by
  have hk : s % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have hN : N + 1 < 2 ^ (N + 1) := Nat.lt_two_pow_self
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hK : 2 ^ (k + (N + 1)) = 2 ^ k * 2 ^ (N + 1) := Nat.pow_add 2 k (N + 1)
  have hlt : s % 2 ^ k + 2 ^ k * (N + 1) < 2 ^ (k + (N + 1)) := by
    rw [hK]
    have : 2 ^ k * (N + 2) ≤ 2 ^ k * 2 ^ (N + 1) := Nat.mul_le_mul_left _ (by omega)
    have : 2 ^ k * (N + 2) = 2 ^ k * (N + 1) + 2 ^ k := by grind
    omega
  obtain ⟨x, -, h2, h3, hr⟩ :=
    counterexample_in_class6 h (k + (N + 1)) (s % 2 ^ k + 2 ^ k * (N + 1)) J t
  rw [Nat.mod_eq_of_lt hlt] at h2
  have hdv : 2 ^ k ∣ 2 ^ (k + (N + 1)) := Nat.pow_dvd_pow 2 (by omega)
  refine ⟨x, ?_, ?_, h3, hr⟩
  · have hx : x % 2 ^ (k + (N + 1)) ≤ x := Nat.mod_le _ _
    have : N + 1 ≤ 2 ^ k * (N + 1) := Nat.le_mul_of_pos_left _ hpos
    omega
  · rw [← Nat.mod_mod_of_dvd x hdv, h2, Nat.add_mul_mod_self_left, Nat.mod_mod]

end Collatz
