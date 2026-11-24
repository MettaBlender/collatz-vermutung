import Collatz.KrasikovClass
import Collatz.ThreeAdic

/-!
# Satz 49: Satz 47 in jeder Restklasse modulo `2^K · 3^J`

Verschärfung von Satz 48: Für **jede** Restklasse `s` modulo `2^K` und **jede** Restklasse `t`
modulo `3^J` (auch durch 3 teilbare) gibt es für jedes `k` mindestens `L₀^k` verschiedene Zahlen
`x` in beiden Klassen mit `3^(50k)·x ≤ 5·2^(classExp6 K J)·2^(163k)`, die alle die 1
erreichen. Wieder hängt nur die Konstante von `K` und `J` ab, der Exponent `0.665` nicht.

Beweis wie Satz 48, aber mit `K+1` statt `K` (dann gibt es einen ungeraden Schritt), mit
`solve_lin` für die Klasse modulo `3^J` und mit der Periode `2·3^(K+1+J)` von 2 modulo
`3^(o+J)`.
-/

namespace Collatz

/-- Ein Vertreter modulo `2^(K+1)` mit mindestens einem ungeraden Schritt. -/
theorem lift_odd (K s : Nat) (hs : s < 2 ^ K) :
    ∃ s'', s'' < 2 ^ (K + 1) ∧ s'' % 2 ^ K = s ∧ 1 ≤ oddsT (K + 1) s'' := by
  have hk1 : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [Nat.pow_succ, Nat.mul_comm]
  by_cases ho : 1 ≤ oddsT K s
  · refine ⟨s, by omega, Nat.mod_eq_of_lt hs, ?_⟩
    rw [oddsT_succ]; omega
  · have ho0 : oddsT K s = 0 := by omega
    by_cases hp : Titer K s % 2 = 1
    · refine ⟨s, by omega, Nat.mod_eq_of_lt hs, ?_⟩
      rw [oddsT_succ, if_pos hp]; omega
    · have haff := (affine K s 1).1
      rw [ho0, Nat.pow_zero, Nat.mul_one, Nat.mul_one] at haff
      refine ⟨s + 2 ^ K, by omega, ?_, ?_⟩
      · rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt hs
      · rw [oddsT_succ, if_pos (by rw [haff]; omega)]; omega

/-- Exponent der Konstanten in Satz 49. -/
def classExp6 (K J : Nat) : Nat :=
  K + 1 + 2 * J + 2 + 2 * 3 ^ (K + 1 + J) * (2 * (K + 1 + J) + 2)

theorem three_pow_le_four_pow (n : Nat) : 3 ^ n ≤ 4 ^ n := Nat.pow_le_pow_left (by decide) n

/-- Ein Vorfahr von `m` in der Klasse `s` mod `2^K'` und `t` mod `3^J`, sofern `s` einen
ungeraden Schritt hat. -/
theorem preimage6 {K' s : Nat} (hs : s < 2 ^ K') (ho1 : 1 ≤ oddsT K' s) (J t m : Nat)
    (hm1 : m % 2 = 1) (hm3 : m % 3 ≠ 0) :
    ∃ x e, x % 2 ^ K' = s ∧ x % 3 ^ J = t % 3 ^ J ∧ Titer K' x = 2 ^ e * m ∧
      x ≤ 2 ^ (K' + 2 * J + 2 + 2 * 3 ^ (K' + J) * (2 * (K' + J) + 2)) * m := by
  have hm0 : 0 < m := by omega
  have hoK := oddsT_le K' s
  have hy3 := Titer_mod_three K' s ho1
  generalize ho : oddsT K' s = o at hoK ho1
  generalize hY : Titer K' s = y at hy3
  have h3J : 0 < 3 ^ J := Nat.pow_pos (by decide)
  obtain ⟨b0, hb0⟩ := solve_lin J K' s t
  -- reduziere b0 modulo 3^J
  have hb0' : (s + 2 ^ K' * (b0 % 3 ^ J)) % 3 ^ J = t % 3 ^ J := by
    rw [← hb0, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
  generalize hb1 : b0 % 3 ^ J = b1 at hb0'
  have hb1lt : b1 < 3 ^ J := by rw [← hb1]; exact Nat.mod_lt _ h3J
  generalize hz : y + 3 ^ o * b1 = z
  have hz3 : z % 3 ≠ 0 := by
    obtain ⟨o', rfl⟩ : ∃ o', o = o' + 1 := ⟨o - 1, by omega⟩
    rw [← hz, Nat.pow_succ, Nat.mul_comm (3 ^ o') 3, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    exact hy3
  -- Schranke für z
  generalize hL : 2 * (K' + J) + 1 = L
  have hzL : z < 2 ^ L := by
    have h1 : y < 4 ^ K' := by
      have := Titer_le K' s
      rw [hY] at this
      have : 2 ^ K' * s < 2 ^ K' * 2 ^ K' := Nat.mul_lt_mul_of_pos_left hs (Nat.two_pow_pos K')
      have : 4 ^ K' = 2 ^ K' * 2 ^ K' := by rw [show 4 = 2 * 2 from rfl, Nat.mul_pow]
      omega
    have h2 : 3 ^ o * b1 < 4 ^ (K' + J) := by
      have : 3 ^ o * b1 < 3 ^ K' * 3 ^ J :=
        Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hoK))
          (Nat.mul_lt_mul_of_pos_left hb1lt (Nat.pow_pos (by decide)))
      rw [← Nat.pow_add] at this
      exact Nat.lt_of_lt_of_le this (three_pow_le_four_pow _)
    have h3 : 4 ^ K' ≤ 4 ^ (K' + J) := Nat.pow_le_pow_right (by decide) (by omega)
    have : 2 ^ L = 2 * 4 ^ (K' + J) := by
      rw [← hL, Nat.pow_succ, Nat.pow_mul, Nat.mul_comm]
    omega
  -- Exponent e
  have hP : 0 < 2 * 3 ^ (K' + J) := by have := Nat.pow_pos (n := K' + J) (show 0 < 3 by decide); omega
  obtain ⟨e0, c0, hc0⟩ := two_pow_hits (o + J) m z hm3 hz3 hm0
  generalize he : e0 % (2 * 3 ^ (K' + J)) + 2 * 3 ^ (K' + J) * L = e
  have he1 : L ≤ e := by
    have : L ≤ 2 * 3 ^ (K' + J) * L := Nat.le_mul_of_pos_left _ hP
    omega
  have he2 : e < 2 * 3 ^ (K' + J) * (2 * (K' + J) + 2) := by
    have := Nat.mod_lt e0 hP
    rw [show 2 * (K' + J) + 2 = L + 1 by omega, Nat.mul_add, Nat.mul_one]; omega
  have hoJ : o + J ≤ K' + J := by omega
  have hcong : 2 ^ e * m % 3 ^ (o + J) = z % 3 ^ (o + J) := by
    have h1 : 2 ^ e0 * m % 3 ^ (o + J) = z % 3 ^ (o + J) := by
      rw [hc0, Nat.add_mul_mod_self_left]
    rw [← he, Nat.mul_mod, two_pow_period hoJ, Nat.add_mul_mod_self_left,
      Nat.mod_mod_of_dvd _ (Nat.dvd_refl _), ← two_pow_period hoJ, ← Nat.mul_mod, h1]
  have hge : z ≤ 2 ^ e * m := by
    have : 2 ^ L ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) he1
    have : 2 ^ e ≤ 2 ^ e * m := Nat.le_mul_of_pos_right _ hm0
    omega
  obtain ⟨c, hc⟩ : 3 ^ (o + J) ∣ 2 ^ e * m - z :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hcong)
  refine ⟨s + 2 ^ K' * (b1 + 3 ^ J * c), e, ?_, ?_, ?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hs
  · have : s + 2 ^ K' * (b1 + 3 ^ J * c) = (s + 2 ^ K' * b1) + 3 ^ J * (2 ^ K' * c) := by
      rw [Nat.mul_add]; ac_rfl
    rw [this, Nat.add_mul_mod_self_left, hb0']
  · rw [(affine K' s _).1, hY, ho]
    have : 3 ^ o * (b1 + 3 ^ J * c) = 3 ^ o * b1 + 3 ^ (o + J) * c := by
      rw [Nat.mul_add, Nat.pow_add, Nat.mul_assoc]
    omega
  · have hc' : c ≤ 2 ^ e * m := by
      have : c ≤ 3 ^ (o + J) * c := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
      omega
    generalize hE : 2 * 3 ^ (K' + J) * (2 * (K' + J) + 2) = E at he2
    have hEe : 2 ^ e ≤ 2 ^ E := Nat.pow_le_pow_right (by decide) (by omega)
    have hJ4 : 3 ^ J ≤ 2 ^ (2 * J) := by
      rw [Nat.pow_mul]; exact three_pow_le_four_pow J
    generalize hM : 2 ^ E * m = M
    have hM1 : 1 ≤ M := by rw [← hM]; exact Nat.mul_pos (Nat.two_pow_pos _) hm0
    have hcM : c ≤ M := by rw [← hM]; exact Nat.le_trans hc' (Nat.mul_le_mul_right _ hEe)
    -- b1 + 3^J c ≤ 3^J (1 + M) ≤ 2^(2J) · 2M
    have hB : b1 + 3 ^ J * c ≤ 2 ^ (2 * J) * (2 * M) := by
      have : 3 ^ J * c ≤ 3 ^ J * M := Nat.mul_le_mul_left _ hcM
      have : 3 ^ J * (2 * M) ≤ 2 ^ (2 * J) * (2 * M) := Nat.mul_le_mul_right _ hJ4
      have : 3 ^ J * (2 * M) = 3 ^ J * M + 3 ^ J * M := by rw [Nat.two_mul, Nat.mul_add]
      have : 3 ^ J ≤ 3 ^ J * M := Nat.le_mul_of_pos_right _ hM1
      omega
    have hx : s + 2 ^ K' * (b1 + 3 ^ J * c) ≤ 2 ^ K' * (2 ^ (2 * J) * (4 * M)) := by
      have : 2 ^ K' * (b1 + 3 ^ J * c) ≤ 2 ^ K' * (2 ^ (2 * J) * (2 * M)) :=
        Nat.mul_le_mul_left _ hB
      have : 2 ^ K' ≤ 2 ^ K' * (2 ^ (2 * J) * (2 * M)) :=
        Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.two_pow_pos _) (by omega))
      have : 2 ^ K' * (2 ^ (2 * J) * (4 * M)) =
          2 ^ K' * (2 ^ (2 * J) * (2 * M)) + 2 ^ K' * (2 ^ (2 * J) * (2 * M)) := by
        rw [← Nat.mul_add, ← Nat.mul_add]; congr 2; omega
      omega
    have : 2 ^ K' * (2 ^ (2 * J) * (4 * M)) = 2 ^ (K' + 2 * J + 2 + E) * m := by
      rw [← hM, Nat.pow_add, Nat.pow_add, Nat.pow_add, show 2 ^ 2 = 4 from rfl]; ac_rfl
    omega

/-- Vorfahr in der Klasse `s mod 2^K`, `t mod 3^J`. -/
theorem class6_preimage (K s J t m : Nat) (hm1 : m % 2 = 1) (hm3 : m % 3 ≠ 0) :
    ∃ x e, x % 2 ^ K = s % 2 ^ K ∧ x % 3 ^ J = t % 3 ^ J ∧ Titer (K + 1) x = 2 ^ e * m ∧
      x ≤ 2 ^ classExp6 K J * m := by
  obtain ⟨s'', h1, h2, h3⟩ := lift_odd K (s % 2 ^ K) (Nat.mod_lt _ (Nat.two_pow_pos K))
  obtain ⟨x, e, a, b, c, d⟩ := preimage6 h1 h3 J t m hm1 hm3
  have hdv : 2 ^ K ∣ 2 ^ (K + 1) := Nat.pow_dvd_pow 2 (by omega)
  refine ⟨x, e, ?_, b, c, ?_⟩
  · rw [← Nat.mod_mod_of_dvd x hdv, a, h2]
  · unfold classExp6; exact d

/-- Injektive Übertragung einer Liste in die Klasse modulo `2^K · 3^J`. -/
theorem class6_lift (K s J t : Nat) : ∀ L : List Nat, L.Nodup →
    (∀ m ∈ L, m % 2 = 1 ∧ m % 3 ≠ 0) →
    ∃ L' : List Nat, L'.Nodup ∧ L'.length = L.length ∧ ∀ x ∈ L', x % 2 ^ K = s % 2 ^ K ∧
      x % 3 ^ J = t % 3 ^ J ∧ ∃ m ∈ L, ∃ e, Titer (K + 1) x = 2 ^ e * m ∧
        x ≤ 2 ^ classExp6 K J * m := by
  intro L
  induction L with
  | nil => intro _ _; exact ⟨[], List.nodup_nil, rfl, by simp⟩
  | cons m L ih =>
    intro hnd hL
    rw [List.nodup_cons] at hnd
    obtain ⟨L', hnd', hlen, hP⟩ := ih hnd.2 (fun m' h => hL m' (List.mem_cons_of_mem _ h))
    obtain ⟨hm1, hm3⟩ := hL m List.mem_cons_self
    obtain ⟨x, e, hx, hx3, hT, hb⟩ := class6_preimage K s J t m hm1 hm3
    refine ⟨x :: L', ?_, by simp [hlen], ?_⟩
    · rw [List.nodup_cons]
      refine ⟨fun hxL => ?_, hnd'⟩
      obtain ⟨-, -, m', hm', e', hT', -⟩ := hP x hxL
      have := odd_part_unique e e' m m' hm1 (hL m' (List.mem_cons_of_mem _ hm')).1
        (by rw [← hT, hT'])
      exact hnd.1 (this ▸ hm')
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨hx, hx3, m, List.mem_cons_self, e, hT, hb⟩
      · obtain ⟨h1, h2, m', hm', e', h3⟩ := hP z hz
        exact ⟨h1, h2, m', List.mem_cons_of_mem _ hm', e', h3⟩

/-- **Satz 49.** In jeder Restklasse `s` modulo `2^K` und zugleich `t` modulo `3^J` gibt es für
jedes `k` mindestens `58 525 359 050 790 615^k` verschiedene Zahlen `x` mit
`3^(50k)·x ≤ 2^(classExp6 K J)·2^(163k)·5`, die alle die 1 erreichen. -/
theorem krasikov_in_class6 (K s J t k : Nat) :
    ∃ L : List Nat, L.Nodup ∧ 58525359050790615 ^ k ≤ L.length ∧
      ∀ x ∈ L, x % 2 ^ K = s % 2 ^ K ∧ x % 3 ^ J = t % 3 ^ J ∧
        3 ^ (k * 50) * x ≤ 2 ^ classExp6 K J * (2 ^ (k * 163) * 5) ∧ ReachesOne x := by
  obtain ⟨q, hc, hq⟩ := cert50
  obtain ⟨L, hn, hl, hg⟩ := block (by decide) hc (Nat.le_refl 50) (Nat.le_refl 163)
    (fun t ht h3 => by rw [hq]; exact final50 t ht h3) k 5 (by decide) (by decide)
  obtain ⟨L', hn', hlen, hP⟩ :=
    class6_lift K s J t L hn (fun m hm => ⟨(hg m hm).1, (hg m hm).2.1⟩)
  refine ⟨L', hn', by omega, fun x hx => ?_⟩
  obtain ⟨hxs, hxt, m, hm, e, hT, hb⟩ := hP x hx
  obtain ⟨-, -, hbd, -, j, hj⟩ := hg m hm
  refine ⟨hxs, hxt, ?_, ?_⟩
  · calc 3 ^ (k * 50) * x ≤ 3 ^ (k * 50) * (2 ^ classExp6 K J * m) := Nat.mul_le_mul_left _ hb
      _ = 2 ^ classExp6 K J * (3 ^ (k * 50) * m) := by ac_rfl
      _ ≤ 2 ^ classExp6 K J * (2 ^ (k * 163) * 5) := Nat.mul_le_mul_left _ hbd
  · obtain ⟨i, hi⟩ := iter_of_Titer hT
    exact ⟨i + j + 5, by rw [iter_add, iter_add, hi, hj]; decide⟩

/-- **Gegenbeispiel-Version.** -/
theorem krasikov_counterexamples_in_class6 (h : ¬ CollatzConjecture) :
    ∃ r, 0 < r ∧ ∀ K s J t k, ∃ L : List Nat, L.Nodup ∧ 58525359050790615 ^ k ≤ L.length ∧
      ∀ x ∈ L, x % 2 ^ K = s % 2 ^ K ∧ x % 3 ^ J = t % 3 ^ J ∧
        3 ^ (k * 50) * x ≤ 2 ^ classExp6 K J * (2 ^ (k * 163) * r) ∧ ¬ ReachesOne x := by
  obtain ⟨n, hn, hr⟩ : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact h (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  obtain ⟨n', hn', h3', hr'⟩ := counterexample_not_three n hn hr
  obtain ⟨r, h0, h1, h3, hrr⟩ := counterexample_odd_not_three n' hn' h3' hr'
  refine ⟨r, h0, fun K s J t k => ?_⟩
  obtain ⟨q, hc, hq⟩ := cert50
  obtain ⟨L, hnd, hl, hg⟩ := block (by decide) hc (Nat.le_refl 50) (Nat.le_refl 163)
    (fun t ht h3 => by rw [hq]; exact final50 t ht h3) k r h1 h3
  obtain ⟨L', hn', hlen, hP⟩ :=
    class6_lift K s J t L hnd (fun m hm => ⟨(hg m hm).1, (hg m hm).2.1⟩)
  refine ⟨L', hn', by omega, fun x hx => ?_⟩
  obtain ⟨hxs, hxt, m, hm, e, hT, hb⟩ := hP x hx
  obtain ⟨-, -, hbd, -, j, hj⟩ := hg m hm
  refine ⟨hxs, hxt, ?_, fun hx1 => ?_⟩
  · calc 3 ^ (k * 50) * x ≤ 3 ^ (k * 50) * (2 ^ classExp6 K J * m) := Nat.mul_le_mul_left _ hb
      _ = 2 ^ classExp6 K J * (3 ^ (k * 50) * m) := by ac_rfl
      _ ≤ 2 ^ classExp6 K J * (2 ^ (k * 163) * r) := Nat.mul_le_mul_left _ hbd
  · obtain ⟨i, hi⟩ := iter_of_Titer hT
    have := reachesOne_iter (reachesOne_iter hx1 i) j
    rw [hi, hj] at this
    exact hrr this

end Collatz
