import Collatz.KrasikovBound
import Collatz.Korec

/-!
# Satz 48: Satz 47 gilt in jeder Restklasse modulo `2^K`

Zu jeder Restklasse `s` modulo `2^K` gibt es für jedes `k` mindestens `L₀^k` verschiedene
Zahlen `x ≡ s (mod 2^K)` mit `3^(50k)·x ≤ C_K·2^(163k)`, die alle die 1 erreichen. Die
Konstante `C_K = 5·2^(K + 2·3^K·(2K+1) + 1)` hängt nur von `K` ab, der Exponent `0.665`
nicht. Keine Restklasse ist also «dünner» als die ganze Zahlenmenge.

Beweisidee: Für `s' = s mod 2^K` gilt nach Terras `T^K(s' + 2^K b) = y + 3^o b` mit
`y = T^K(s')`, `o ≤ K`. Zu jedem Knoten `m` aus Satz 47 (ungerade, `3 ∤ m`) wählt man `e`
mit `2^e m ≡ y (mod 3^o)`; da `2` modulo `3^o` die Periode `2·3^K` hat (Hebung
`four_lift`), geht das mit beschränktem `e`. Dann ist `x = s' + 2^K b` mit
`y + 3^o b = 2^e m` in der Klasse, `T^(K+e)(x) = m`, und `x` bestimmt `m` (ungerader Anteil
von `T^K x`). So wird die Liste aus Satz 47 injektiv in die Restklasse abgebildet.
-/

namespace Collatz

/-- Periode von `2` modulo `3^o` (für `o ≤ K`). -/
theorem two_pow_period {o K : Nat} (ho : o ≤ K) (a : Nat) :
    2 ^ a % 3 ^ o = 2 ^ (a % (2 * 3 ^ K)) % 3 ^ o := by
  obtain ⟨w, -, hw⟩ := four_lift K
  have hP : 2 ^ (2 * 3 ^ K) % 3 ^ o = 1 % 3 ^ o := by
    have e1 : 2 ^ (2 * 3 ^ K) = 4 ^ (3 ^ K) := by rw [Nat.pow_mul]
    have e2 : 3 ^ (K + 1) = 3 ^ o * 3 ^ (K + 1 - o) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [e1, hw, e2, Nat.mul_assoc, Nat.add_mul_mod_self_left]
  conv => lhs; rw [← Nat.mod_add_div a (2 * 3 ^ K)]
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod (2 ^ (2 * 3 ^ K)), hP,
    ← Nat.pow_mod, Nat.one_pow, Nat.mul_mod_mod, Nat.mul_one, Nat.mod_mod]

theorem T_le_two_mul (n : Nat) : T n ≤ 2 * n := by
  unfold T; split <;> omega

theorem Titer_le : ∀ k n, Titer k n ≤ 2 ^ k * n := by
  intro k
  induction k with
  | zero => intro n; simp [Titer]
  | succ k ih =>
    intro n
    simp only [Titer]
    calc Titer k (T n) ≤ 2 ^ k * T n := ih _
      _ ≤ 2 ^ k * (2 * n) := Nat.mul_le_mul_left _ (T_le_two_mul n)
      _ = 2 ^ (k + 1) * n := by rw [Nat.pow_succ]; ac_rfl

/-- Exponent der Konstanten. -/
def classExp (K : Nat) : Nat := K + 2 * 3 ^ K * (2 * K + 1) + 1

/-- Ein Vorfahr von `m` in der Klasse `s mod 2^K`. -/
theorem class_preimage (K s m : Nat) (hm1 : m % 2 = 1) (hm3 : m % 3 ≠ 0) :
    ∃ x e, x % 2 ^ K = s % 2 ^ K ∧ Titer K x = 2 ^ e * m ∧ x ≤ 2 ^ classExp K * m := by
  generalize hs' : s % 2 ^ K = s'
  have hlt : s' < 2 ^ K := by rw [← hs']; exact Nat.mod_lt _ (Nat.two_pow_pos K)
  have hm0 : 0 < m := by omega
  have hoK := oddsT_le K s'
  generalize ho : oddsT K s' = o at hoK
  generalize hy : Titer K s' = y
  have hyb : y < 2 ^ (2 * K) := by
    have := Titer_le K s'
    rw [hy] at this
    have : 2 ^ K * s' < 2 ^ K * 2 ^ K := Nat.mul_lt_mul_of_pos_left hlt (Nat.two_pow_pos K)
    rw [Nat.two_mul, Nat.pow_add]; omega
  -- ein Exponent `e` mit `2K ≤ e`, `e < P(2K+1)` und `2^e m ≡ y (mod 3^o)`
  have hP : 0 < 2 * 3 ^ K := by have := Nat.pow_pos (n := K) (show 0 < 3 by decide); omega
  obtain ⟨e, he1, he2, hcong⟩ : ∃ e, 2 * K ≤ e ∧ e < 2 * 3 ^ K * (2 * K + 1) ∧
      2 ^ e * m % 3 ^ o = y % 3 ^ o := by
    by_cases h0 : o = 0
    · subst h0
      refine ⟨2 * K, ?_, ?_, by simp [Nat.mod_one]⟩
      · omega
      · have : 2 * K < 2 * 3 ^ K * (2 * K) + 2 * 3 ^ K := by
          have : 2 * K ≤ 2 * 3 ^ K * (2 * K) := Nat.le_mul_of_pos_left _ hP
          omega
        rw [Nat.mul_add, Nat.mul_one]; exact this
    · obtain ⟨e0, b0, h⟩ := two_pow_hits o m y hm3
        (by rw [← hy, ← ho] at *; exact Titer_mod_three K s' (by omega)) hm0
      refine ⟨e0 % (2 * 3 ^ K) + 2 * 3 ^ K * (2 * K), ?_, ?_, ?_⟩
      · have : 2 * K ≤ 2 * 3 ^ K * (2 * K) := Nat.le_mul_of_pos_left _ hP
        omega
      · have := Nat.mod_lt e0 hP
        rw [Nat.mul_add, Nat.mul_one]; omega
      · have h1 : 2 ^ e0 * m % 3 ^ o = y % 3 ^ o := by
          rw [h, Nat.add_mul_mod_self_left]
        rw [Nat.mul_mod, two_pow_period hoK, Nat.add_mul_mod_self_left,
          Nat.mod_mod_of_dvd, ← two_pow_period hoK, ← Nat.mul_mod, h1]
        exact Nat.dvd_refl _
  have hge : y ≤ 2 ^ e * m := by
    have : 2 ^ (2 * K) ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) he1
    have : 2 ^ e ≤ 2 ^ e * m := Nat.le_mul_of_pos_right _ hm0
    omega
  have hdvd : 3 ^ o ∣ 2 ^ e * m - y :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hcong)
  obtain ⟨b, hb⟩ := hdvd
  refine ⟨s' + 2 ^ K * b, e, ?_, ?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hlt
  · rw [(affine K s' b).1, hy, ho, ← hb]; omega
  · have hb' : b ≤ 2 ^ e * m := by
      have : b ≤ 3 ^ o * b := Nat.le_mul_of_pos_left _ (Nat.pow_pos (n := o) (show 0 < 3 by decide))
      omega
    have hE : 2 ^ e ≤ 2 ^ (2 * 3 ^ K * (2 * K + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    have : 2 ^ K * b ≤ 2 ^ K * (2 ^ (2 * 3 ^ K * (2 * K + 1)) * m) :=
      Nat.mul_le_mul_left _ (Nat.le_trans hb' (Nat.mul_le_mul_right _ hE))
    have hk : 2 ^ K ≤ 2 ^ K * (2 ^ (2 * 3 ^ K * (2 * K + 1)) * m) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.two_pow_pos _) hm0)
    have : 2 ^ classExp K * m = 2 * (2 ^ K * (2 ^ (2 * 3 ^ K * (2 * K + 1)) * m)) := by
      unfold classExp; rw [Nat.pow_succ, Nat.pow_add]; ac_rfl
    omega

/-- Injektive Übertragung einer Liste in die Restklasse. -/
theorem class_lift (K s : Nat) : ∀ L : List Nat, L.Nodup → (∀ m ∈ L, m % 2 = 1 ∧ m % 3 ≠ 0) →
    ∃ L' : List Nat, L'.Nodup ∧ L'.length = L.length ∧ ∀ x ∈ L', x % 2 ^ K = s % 2 ^ K ∧
      ∃ m ∈ L, ∃ e, Titer K x = 2 ^ e * m ∧ x ≤ 2 ^ classExp K * m := by
  intro L
  induction L with
  | nil => intro _ _; exact ⟨[], List.nodup_nil, rfl, by simp⟩
  | cons m L ih =>
    intro hnd hL
    rw [List.nodup_cons] at hnd
    obtain ⟨L', hnd', hlen, hP⟩ := ih hnd.2 (fun m' h => hL m' (List.mem_cons_of_mem _ h))
    obtain ⟨hm1, hm3⟩ := hL m List.mem_cons_self
    obtain ⟨x, e, hx, hT, hb⟩ := class_preimage K s m hm1 hm3
    refine ⟨x :: L', ?_, by simp [hlen], ?_⟩
    · rw [List.nodup_cons]
      refine ⟨fun hxL => ?_, hnd'⟩
      obtain ⟨-, m', hm', e', hT', -⟩ := hP x hxL
      have := odd_part_unique e e' m m' hm1 (hL m' (List.mem_cons_of_mem _ hm')).1
        (by rw [← hT, hT'])
      exact hnd.1 (this ▸ hm')
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨hx, m, List.mem_cons_self, e, hT, hb⟩
      · obtain ⟨h1, m', hm', e', h2⟩ := hP z hz
        exact ⟨h1, m', List.mem_cons_of_mem _ hm', e', h2⟩

/-- Aus `T^K x = 2^e m` folgt: `x` erreicht `m` unter `step`. -/
theorem iter_of_Titer {K x e m : Nat} (h : Titer K x = 2 ^ e * m) : ∃ j, iter j x = m := by
  refine ⟨(K + oddsT K x) + (e + oddsT e (2 ^ e * m)), ?_⟩
  rw [iter_add, ← Titer_eq_iter, h, ← Titer_eq_iter, Titer_two_pow]

/-- **Satz 48.** In jeder Restklasse `s` modulo `2^K` gibt es für jedes `k` mindestens
`58 525 359 050 790 615^k` verschiedene Zahlen `x` mit `3^(50k)·x ≤ 5·2^(classExp K)·2^(163k)`,
die alle die 1 erreichen. -/
theorem krasikov_in_class (K s k : Nat) :
    ∃ L : List Nat, L.Nodup ∧ 58525359050790615 ^ k ≤ L.length ∧
      ∀ x ∈ L, x % 2 ^ K = s % 2 ^ K ∧
        3 ^ (k * 50) * x ≤ 2 ^ classExp K * (2 ^ (k * 163) * 5) ∧ ReachesOne x := by
  obtain ⟨q, hc, hq⟩ := cert50
  obtain ⟨L, hn, hl, hg⟩ := block (by decide) hc (Nat.le_refl 50) (Nat.le_refl 163)
    (fun t ht h3 => by rw [hq]; exact final50 t ht h3) k 5 (by decide) (by decide)
  obtain ⟨L', hn', hlen, hP⟩ := class_lift K s L hn (fun m hm => ⟨(hg m hm).1, (hg m hm).2.1⟩)
  refine ⟨L', hn', by omega, fun x hx => ?_⟩
  obtain ⟨hxs, m, hm, e, hT, hb⟩ := hP x hx
  obtain ⟨-, -, hbd, -, j, hj⟩ := hg m hm
  refine ⟨hxs, ?_, ?_⟩
  · calc 3 ^ (k * 50) * x ≤ 3 ^ (k * 50) * (2 ^ classExp K * m) := Nat.mul_le_mul_left _ hb
      _ = 2 ^ classExp K * (3 ^ (k * 50) * m) := by ac_rfl
      _ ≤ 2 ^ classExp K * (2 ^ (k * 163) * 5) := Nat.mul_le_mul_left _ hbd
  · obtain ⟨i, hi⟩ := iter_of_Titer hT
    exact ⟨i + j + 5, by rw [iter_add, iter_add, hi, hj]; decide⟩

/-- **Gegenbeispiel-Version.** Gäbe es ein Gegenbeispiel, so enthielte jede Restklasse modulo
`2^K` ebenso viele Gegenbeispiele (bis auf eine nur von `K` abhängige Konstante). -/
theorem krasikov_counterexamples_in_class (h : ¬ CollatzConjecture) :
    ∃ r, 0 < r ∧ ∀ K s k, ∃ L : List Nat, L.Nodup ∧ 58525359050790615 ^ k ≤ L.length ∧
      ∀ x ∈ L, x % 2 ^ K = s % 2 ^ K ∧
        3 ^ (k * 50) * x ≤ 2 ^ classExp K * (2 ^ (k * 163) * r) ∧ ¬ ReachesOne x := by
  obtain ⟨n, hn, hr⟩ : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hne
    exact h (fun n hn => Classical.byContradiction (fun hr => hne ⟨n, hn, hr⟩))
  obtain ⟨n', hn', h3', hr'⟩ := counterexample_not_three n hn hr
  obtain ⟨r, h0, h1, h3, hrr⟩ := counterexample_odd_not_three n' hn' h3' hr'
  refine ⟨r, h0, fun K s k => ?_⟩
  obtain ⟨q, hc, hq⟩ := cert50
  obtain ⟨L, hnd, hl, hg⟩ := block (by decide) hc (Nat.le_refl 50) (Nat.le_refl 163)
    (fun t ht h3 => by rw [hq]; exact final50 t ht h3) k r h1 h3
  obtain ⟨L', hn', hlen, hP⟩ := class_lift K s L hnd (fun m hm => ⟨(hg m hm).1, (hg m hm).2.1⟩)
  refine ⟨L', hn', by omega, fun x hx => ?_⟩
  obtain ⟨hxs, m, hm, e, hT, hb⟩ := hP x hx
  obtain ⟨-, -, hbd, -, j, hj⟩ := hg m hm
  refine ⟨hxs, ?_, fun hx1 => ?_⟩
  · calc 3 ^ (k * 50) * x ≤ 3 ^ (k * 50) * (2 ^ classExp K * m) := Nat.mul_le_mul_left _ hb
      _ = 2 ^ classExp K * (3 ^ (k * 50) * m) := by ac_rfl
      _ ≤ 2 ^ classExp K * (2 ^ (k * 163) * r) := Nat.mul_le_mul_left _ hbd
  · obtain ⟨i, hi⟩ := iter_of_Titer hT
    have := reachesOne_iter (reachesOne_iter hx1 i) j
    rw [hi, hj] at this
    exact hrr this

end Collatz
