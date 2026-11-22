import Collatz.VerifiedHugeA
import Collatz.VerifiedHugeB
import Collatz.VerifiedHugeC
import Collatz.VerifiedHugeD
import Collatz.VerifiedHugeE
import Collatz.VerifiedHugeF
import Collatz.VerifiedHugeG
import Collatz.VerifiedHugeH
import Collatz.CycleCheck

/-!
# Folgerungen aus der Rechnung bis 2^22

* Alle Zahlen `1 ≤ n < 2^22 = 4 194 304` erreichen die 1.
* Ein nichttrivialer Zyklus enthält nur Zahlen `≥ 2^22`.
* Deshalb hätte er mindestens 7621 ungerade Glieder und mindestens 19 700 Schritte.
* Das kleinste Glied eines Gegenbeispiels ist `≥ 2^22` und liegt in einer der 27 328
  offenen Restklassen modulo `2^20`.
-/

namespace Collatz

/-- **Jede Zahl `1 < m < 2^22` fällt unter sich selbst.** -/
theorem descends_below_2_22 : ∀ m, 1 < m → m < 4194304 → Descends m := by
  intro m h1 hm
  have hm' : m < 65536 * 64 := hm
  by_cases c0 : m % 65536 < 1024
  · exact descends_of_verifyOpen huge0 (by omega) (by omega) hm' h1
  by_cases c1 : m % 65536 < 2048
  · exact descends_of_verifyOpen huge1 (by omega) (by omega) hm' h1
  by_cases c2 : m % 65536 < 3072
  · exact descends_of_verifyOpen huge2 (by omega) (by omega) hm' h1
  by_cases c3 : m % 65536 < 4096
  · exact descends_of_verifyOpen huge3 (by omega) (by omega) hm' h1
  by_cases c4 : m % 65536 < 5120
  · exact descends_of_verifyOpen huge4 (by omega) (by omega) hm' h1
  by_cases c5 : m % 65536 < 6144
  · exact descends_of_verifyOpen huge5 (by omega) (by omega) hm' h1
  by_cases c6 : m % 65536 < 7168
  · exact descends_of_verifyOpen huge6 (by omega) (by omega) hm' h1
  by_cases c7 : m % 65536 < 8192
  · exact descends_of_verifyOpen huge7 (by omega) (by omega) hm' h1
  by_cases c8 : m % 65536 < 9216
  · exact descends_of_verifyOpen huge8 (by omega) (by omega) hm' h1
  by_cases c9 : m % 65536 < 10240
  · exact descends_of_verifyOpen huge9 (by omega) (by omega) hm' h1
  by_cases c10 : m % 65536 < 11264
  · exact descends_of_verifyOpen huge10 (by omega) (by omega) hm' h1
  by_cases c11 : m % 65536 < 12288
  · exact descends_of_verifyOpen huge11 (by omega) (by omega) hm' h1
  by_cases c12 : m % 65536 < 13312
  · exact descends_of_verifyOpen huge12 (by omega) (by omega) hm' h1
  by_cases c13 : m % 65536 < 14336
  · exact descends_of_verifyOpen huge13 (by omega) (by omega) hm' h1
  by_cases c14 : m % 65536 < 15360
  · exact descends_of_verifyOpen huge14 (by omega) (by omega) hm' h1
  by_cases c15 : m % 65536 < 16384
  · exact descends_of_verifyOpen huge15 (by omega) (by omega) hm' h1
  by_cases c16 : m % 65536 < 17408
  · exact descends_of_verifyOpen huge16 (by omega) (by omega) hm' h1
  by_cases c17 : m % 65536 < 18432
  · exact descends_of_verifyOpen huge17 (by omega) (by omega) hm' h1
  by_cases c18 : m % 65536 < 19456
  · exact descends_of_verifyOpen huge18 (by omega) (by omega) hm' h1
  by_cases c19 : m % 65536 < 20480
  · exact descends_of_verifyOpen huge19 (by omega) (by omega) hm' h1
  by_cases c20 : m % 65536 < 21504
  · exact descends_of_verifyOpen huge20 (by omega) (by omega) hm' h1
  by_cases c21 : m % 65536 < 22528
  · exact descends_of_verifyOpen huge21 (by omega) (by omega) hm' h1
  by_cases c22 : m % 65536 < 23552
  · exact descends_of_verifyOpen huge22 (by omega) (by omega) hm' h1
  by_cases c23 : m % 65536 < 24576
  · exact descends_of_verifyOpen huge23 (by omega) (by omega) hm' h1
  by_cases c24 : m % 65536 < 25600
  · exact descends_of_verifyOpen huge24 (by omega) (by omega) hm' h1
  by_cases c25 : m % 65536 < 26624
  · exact descends_of_verifyOpen huge25 (by omega) (by omega) hm' h1
  by_cases c26 : m % 65536 < 27648
  · exact descends_of_verifyOpen huge26 (by omega) (by omega) hm' h1
  by_cases c27 : m % 65536 < 28672
  · exact descends_of_verifyOpen huge27 (by omega) (by omega) hm' h1
  by_cases c28 : m % 65536 < 29696
  · exact descends_of_verifyOpen huge28 (by omega) (by omega) hm' h1
  by_cases c29 : m % 65536 < 30720
  · exact descends_of_verifyOpen huge29 (by omega) (by omega) hm' h1
  by_cases c30 : m % 65536 < 31744
  · exact descends_of_verifyOpen huge30 (by omega) (by omega) hm' h1
  by_cases c31 : m % 65536 < 32768
  · exact descends_of_verifyOpen huge31 (by omega) (by omega) hm' h1
  by_cases c32 : m % 65536 < 33792
  · exact descends_of_verifyOpen huge32 (by omega) (by omega) hm' h1
  by_cases c33 : m % 65536 < 34816
  · exact descends_of_verifyOpen huge33 (by omega) (by omega) hm' h1
  by_cases c34 : m % 65536 < 35840
  · exact descends_of_verifyOpen huge34 (by omega) (by omega) hm' h1
  by_cases c35 : m % 65536 < 36864
  · exact descends_of_verifyOpen huge35 (by omega) (by omega) hm' h1
  by_cases c36 : m % 65536 < 37888
  · exact descends_of_verifyOpen huge36 (by omega) (by omega) hm' h1
  by_cases c37 : m % 65536 < 38912
  · exact descends_of_verifyOpen huge37 (by omega) (by omega) hm' h1
  by_cases c38 : m % 65536 < 39936
  · exact descends_of_verifyOpen huge38 (by omega) (by omega) hm' h1
  by_cases c39 : m % 65536 < 40960
  · exact descends_of_verifyOpen huge39 (by omega) (by omega) hm' h1
  by_cases c40 : m % 65536 < 41984
  · exact descends_of_verifyOpen huge40 (by omega) (by omega) hm' h1
  by_cases c41 : m % 65536 < 43008
  · exact descends_of_verifyOpen huge41 (by omega) (by omega) hm' h1
  by_cases c42 : m % 65536 < 44032
  · exact descends_of_verifyOpen huge42 (by omega) (by omega) hm' h1
  by_cases c43 : m % 65536 < 45056
  · exact descends_of_verifyOpen huge43 (by omega) (by omega) hm' h1
  by_cases c44 : m % 65536 < 46080
  · exact descends_of_verifyOpen huge44 (by omega) (by omega) hm' h1
  by_cases c45 : m % 65536 < 47104
  · exact descends_of_verifyOpen huge45 (by omega) (by omega) hm' h1
  by_cases c46 : m % 65536 < 48128
  · exact descends_of_verifyOpen huge46 (by omega) (by omega) hm' h1
  by_cases c47 : m % 65536 < 49152
  · exact descends_of_verifyOpen huge47 (by omega) (by omega) hm' h1
  by_cases c48 : m % 65536 < 50176
  · exact descends_of_verifyOpen huge48 (by omega) (by omega) hm' h1
  by_cases c49 : m % 65536 < 51200
  · exact descends_of_verifyOpen huge49 (by omega) (by omega) hm' h1
  by_cases c50 : m % 65536 < 52224
  · exact descends_of_verifyOpen huge50 (by omega) (by omega) hm' h1
  by_cases c51 : m % 65536 < 53248
  · exact descends_of_verifyOpen huge51 (by omega) (by omega) hm' h1
  by_cases c52 : m % 65536 < 54272
  · exact descends_of_verifyOpen huge52 (by omega) (by omega) hm' h1
  by_cases c53 : m % 65536 < 55296
  · exact descends_of_verifyOpen huge53 (by omega) (by omega) hm' h1
  by_cases c54 : m % 65536 < 56320
  · exact descends_of_verifyOpen huge54 (by omega) (by omega) hm' h1
  by_cases c55 : m % 65536 < 57344
  · exact descends_of_verifyOpen huge55 (by omega) (by omega) hm' h1
  by_cases c56 : m % 65536 < 58368
  · exact descends_of_verifyOpen huge56 (by omega) (by omega) hm' h1
  by_cases c57 : m % 65536 < 59392
  · exact descends_of_verifyOpen huge57 (by omega) (by omega) hm' h1
  by_cases c58 : m % 65536 < 60416
  · exact descends_of_verifyOpen huge58 (by omega) (by omega) hm' h1
  by_cases c59 : m % 65536 < 61440
  · exact descends_of_verifyOpen huge59 (by omega) (by omega) hm' h1
  by_cases c60 : m % 65536 < 62464
  · exact descends_of_verifyOpen huge60 (by omega) (by omega) hm' h1
  by_cases c61 : m % 65536 < 63488
  · exact descends_of_verifyOpen huge61 (by omega) (by omega) hm' h1
  by_cases c62 : m % 65536 < 64512
  · exact descends_of_verifyOpen huge62 (by omega) (by omega) hm' h1
  have c63 : m % 65536 < 65536 := Nat.mod_lt _ (by decide)
  exact descends_of_verifyOpen huge63 (by omega) (by omega) hm' h1

/-- **Alle Zahlen von 1 bis 2^22 − 1 = 4 194 303 erreichen die 1** (Sieb + Kernel-Rechnung). -/
theorem reachesOne_below_2_22 : ∀ n, 0 < n → n < 4194304 → ReachesOne n := by
  intro n h0 h
  exact reachesOne_of_descends_upto 4194303 (fun m h1 hm => descends_below_2_22 m h1 (by omega))
    n h0 (by omega)

/-- **Ein nichttrivialer Zyklus enthält nur Zahlen `≥ 2^22`.** -/
theorem nontrivial_cycle_ge_2_22 {n p : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : ∀ k, 4194304 ≤ iter k n := by
  intro k
  have hr : ¬ ReachesOne n := fun hr => by
    rcases periodic_reachesOne hp hr with h | h | h <;> omega
  refine Nat.le_of_not_lt (fun hk => ?_)
  exact hr (reachesOne_of_iter (reachesOne_below_2_22 _ (iter_pos h0 k) hk))

/-- Kernel-Rechnung (in wenigen Sekunden): die Zyklus-Ungleichung schliesst für `m = 2^22`
alle `1 ≤ j ≤ 7620` aus. -/
theorem cycleCheck_7620 : cycleCheck 4194304 7620 1 1 1 2 = true := by decide +kernel

/-- **Jeder nichttriviale Zyklus hat mindestens 7621 ungerade Glieder.** -/
theorem cycle_odd_ge_7621 {n p : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : 7621 ≤ oddCount n p :=
  cycle_odd_gt hp h0 (nontrivial_cycle_ge_2_22 hp h0 hnt) cycleCheck_7620

set_option exponentiation.threshold 20000 in
/-- **Jeder nichttriviale Zyklus hat mindestens 19 700 Schritte**
(mindestens 7621 ungerade und 12 079 gerade Glieder). -/
theorem cycle_length_ge_19700 {n p : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : 12079 ≤ evenCount n p ∧ 19700 ≤ p := by
  have hj := cycle_odd_ge_7621 hp h0 hnt
  have hbig := nontrivial_cycle_ge_2_22 hp h0 hnt
  obtain ⟨_, h3, _⟩ := cycle_inequalities (m := 4194304) hp h0 hbig
  have hsum := odd_add_even n p
  have h7621 : 3 ^ 7621 ≤ 3 ^ oddCount n p := Nat.pow_le_pow_right (by decide) hj
  have hpow : 2 ^ 12078 < 3 ^ 7621 := by decide +kernel
  have he : 12078 < evenCount n p := by
    have : 2 ^ 12078 < 2 ^ evenCount n p := by omega
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp this
  omega

/-- **Das kleinste Glied eines Gegenbeispiels liegt in einer offenen Klasse modulo 2^20.** -/
theorem orbitMin_mem_survivors20 {m : Nat} (h1 : 1 < m) (hmin : IsOrbitMin m) :
    m % 1048576 ∈ survivors20 := by
  have hnd : ∀ k, ¬ iter k m < m := fun k hk => absurd (hmin k) (by omega)
  cases h16 : check 65536 (m % 65536) 100 65536 (m % 65536) with
  | true =>
    obtain ⟨k, hk⟩ := descends_of_check h16 rfl h1
    exact absurd hk (hnd k)
  | false =>
    cases h20 : check 1048576 (m % 1048576) 100 1048576 (m % 1048576) with
    | true =>
      obtain ⟨k, hk⟩ := descends_of_check h20 rfl h1
      exact absurd hk (hnd k)
    | false =>
      have ht : m % 1048576 = m % 65536 + 65536 * (m % 1048576 / 65536) := by omega
      have hm := mem_openIn h16 65536 0 (Nat.zero_le _) (by omega)
      rw [ht] at h20
      have := mem_lift (K := 16) hm (by omega) h20
      rwa [← ht] at this

/-- **Struktur eines Gegenbeispiels**: Erreicht `n > 0` die 1 nicht, so enthält seine Folge
ein kleinstes Glied `m ≥ 2^22`, das nie unterschritten wird und dessen Rest modulo `2^20`
eine der 27 328 offenen Restklassen ist. -/
theorem counterexample_structure22 {n : Nat} (h0 : 0 < n) (h : ¬ ReachesOne n) :
    ∃ k, 4194304 ≤ iter k n ∧ IsOrbitMin (iter k n) ∧ iter k n % 1048576 ∈ survivors20 := by
  obtain ⟨k, hk⟩ := exists_orbitMin n
  have hbig : 4194304 ≤ iter k n := by
    refine Nat.le_of_not_lt (fun hlt => ?_)
    exact h (reachesOne_of_iter (reachesOne_below_2_22 _ (iter_pos h0 k) hlt))
  exact ⟨k, hbig, hk, orbitMin_mem_survivors20 (by omega) hk⟩

end Collatz
