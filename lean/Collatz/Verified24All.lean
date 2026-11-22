import Collatz.V24.F00
import Collatz.V24.F01
import Collatz.V24.F02
import Collatz.V24.F03
import Collatz.V24.F04
import Collatz.V24.F05
import Collatz.V24.F06
import Collatz.V24.F07
import Collatz.V24.F08
import Collatz.V24.F09
import Collatz.V24.F10
import Collatz.V24.F11
import Collatz.V24.F12
import Collatz.V24.F13
import Collatz.V24.F14
import Collatz.V24.F15
import Collatz.V24.F16
import Collatz.V24.F17
import Collatz.V24.F18
import Collatz.V24.F19
import Collatz.V24.F20
import Collatz.V24.F21
import Collatz.V24.F22
import Collatz.V24.F23
import Collatz.V24.F24
import Collatz.V24.F25
import Collatz.V24.F26
import Collatz.V24.F27
import Collatz.V24.F28
import Collatz.V24.F29
import Collatz.V24.F30
import Collatz.V24.F31
import Collatz.VerifiedHugeAll

/-!
# Folgerungen aus der Rechnung bis 2^24

* Alle Zahlen `1 ≤ n < 2^24 = 16 777 216` erreichen die 1.
* Ein nichttrivialer Zyklus enthält nur Zahlen `≥ 2^24`.
* Deshalb hätte er mindestens 12 276 ungerade Glieder und mindestens 31 733 Schritte.
* Das kleinste Glied eines Gegenbeispiels ist `≥ 2^24` und liegt in einer der 27 328
  offenen Restklassen modulo `2^20`.
-/

namespace Collatz

theorem verifyOpen24_join' {a b c : Nat} (h1 : verifyOpen24 0 a = true)
    (h2 : verifyOpen24 a b = true) (hc : a + b = c) : verifyOpen24 0 c = true :=
  hc ▸ verifyOpen24_join h1 h2

/-- Die 128 Blöcke zusammen: alle offenen Klassen modulo `2^20`. -/
theorem verifyOpen24_all : verifyOpen24 0 65536 = true := by
  have s0 : verifyOpen24 0 512 = true := v24_0
  have s1 : verifyOpen24 0 1024 = true := verifyOpen24_join' s0 v24_1 (by decide)
  have s2 : verifyOpen24 0 1536 = true := verifyOpen24_join' s1 v24_2 (by decide)
  have s3 : verifyOpen24 0 2048 = true := verifyOpen24_join' s2 v24_3 (by decide)
  have s4 : verifyOpen24 0 2560 = true := verifyOpen24_join' s3 v24_4 (by decide)
  have s5 : verifyOpen24 0 3072 = true := verifyOpen24_join' s4 v24_5 (by decide)
  have s6 : verifyOpen24 0 3584 = true := verifyOpen24_join' s5 v24_6 (by decide)
  have s7 : verifyOpen24 0 4096 = true := verifyOpen24_join' s6 v24_7 (by decide)
  have s8 : verifyOpen24 0 4608 = true := verifyOpen24_join' s7 v24_8 (by decide)
  have s9 : verifyOpen24 0 5120 = true := verifyOpen24_join' s8 v24_9 (by decide)
  have s10 : verifyOpen24 0 5632 = true := verifyOpen24_join' s9 v24_10 (by decide)
  have s11 : verifyOpen24 0 6144 = true := verifyOpen24_join' s10 v24_11 (by decide)
  have s12 : verifyOpen24 0 6656 = true := verifyOpen24_join' s11 v24_12 (by decide)
  have s13 : verifyOpen24 0 7168 = true := verifyOpen24_join' s12 v24_13 (by decide)
  have s14 : verifyOpen24 0 7680 = true := verifyOpen24_join' s13 v24_14 (by decide)
  have s15 : verifyOpen24 0 8192 = true := verifyOpen24_join' s14 v24_15 (by decide)
  have s16 : verifyOpen24 0 8704 = true := verifyOpen24_join' s15 v24_16 (by decide)
  have s17 : verifyOpen24 0 9216 = true := verifyOpen24_join' s16 v24_17 (by decide)
  have s18 : verifyOpen24 0 9728 = true := verifyOpen24_join' s17 v24_18 (by decide)
  have s19 : verifyOpen24 0 10240 = true := verifyOpen24_join' s18 v24_19 (by decide)
  have s20 : verifyOpen24 0 10752 = true := verifyOpen24_join' s19 v24_20 (by decide)
  have s21 : verifyOpen24 0 11264 = true := verifyOpen24_join' s20 v24_21 (by decide)
  have s22 : verifyOpen24 0 11776 = true := verifyOpen24_join' s21 v24_22 (by decide)
  have s23 : verifyOpen24 0 12288 = true := verifyOpen24_join' s22 v24_23 (by decide)
  have s24 : verifyOpen24 0 12800 = true := verifyOpen24_join' s23 v24_24 (by decide)
  have s25 : verifyOpen24 0 13312 = true := verifyOpen24_join' s24 v24_25 (by decide)
  have s26 : verifyOpen24 0 13824 = true := verifyOpen24_join' s25 v24_26 (by decide)
  have s27 : verifyOpen24 0 14336 = true := verifyOpen24_join' s26 v24_27 (by decide)
  have s28 : verifyOpen24 0 14848 = true := verifyOpen24_join' s27 v24_28 (by decide)
  have s29 : verifyOpen24 0 15360 = true := verifyOpen24_join' s28 v24_29 (by decide)
  have s30 : verifyOpen24 0 15872 = true := verifyOpen24_join' s29 v24_30 (by decide)
  have s31 : verifyOpen24 0 16384 = true := verifyOpen24_join' s30 v24_31 (by decide)
  have s32 : verifyOpen24 0 16896 = true := verifyOpen24_join' s31 v24_32 (by decide)
  have s33 : verifyOpen24 0 17408 = true := verifyOpen24_join' s32 v24_33 (by decide)
  have s34 : verifyOpen24 0 17920 = true := verifyOpen24_join' s33 v24_34 (by decide)
  have s35 : verifyOpen24 0 18432 = true := verifyOpen24_join' s34 v24_35 (by decide)
  have s36 : verifyOpen24 0 18944 = true := verifyOpen24_join' s35 v24_36 (by decide)
  have s37 : verifyOpen24 0 19456 = true := verifyOpen24_join' s36 v24_37 (by decide)
  have s38 : verifyOpen24 0 19968 = true := verifyOpen24_join' s37 v24_38 (by decide)
  have s39 : verifyOpen24 0 20480 = true := verifyOpen24_join' s38 v24_39 (by decide)
  have s40 : verifyOpen24 0 20992 = true := verifyOpen24_join' s39 v24_40 (by decide)
  have s41 : verifyOpen24 0 21504 = true := verifyOpen24_join' s40 v24_41 (by decide)
  have s42 : verifyOpen24 0 22016 = true := verifyOpen24_join' s41 v24_42 (by decide)
  have s43 : verifyOpen24 0 22528 = true := verifyOpen24_join' s42 v24_43 (by decide)
  have s44 : verifyOpen24 0 23040 = true := verifyOpen24_join' s43 v24_44 (by decide)
  have s45 : verifyOpen24 0 23552 = true := verifyOpen24_join' s44 v24_45 (by decide)
  have s46 : verifyOpen24 0 24064 = true := verifyOpen24_join' s45 v24_46 (by decide)
  have s47 : verifyOpen24 0 24576 = true := verifyOpen24_join' s46 v24_47 (by decide)
  have s48 : verifyOpen24 0 25088 = true := verifyOpen24_join' s47 v24_48 (by decide)
  have s49 : verifyOpen24 0 25600 = true := verifyOpen24_join' s48 v24_49 (by decide)
  have s50 : verifyOpen24 0 26112 = true := verifyOpen24_join' s49 v24_50 (by decide)
  have s51 : verifyOpen24 0 26624 = true := verifyOpen24_join' s50 v24_51 (by decide)
  have s52 : verifyOpen24 0 27136 = true := verifyOpen24_join' s51 v24_52 (by decide)
  have s53 : verifyOpen24 0 27648 = true := verifyOpen24_join' s52 v24_53 (by decide)
  have s54 : verifyOpen24 0 28160 = true := verifyOpen24_join' s53 v24_54 (by decide)
  have s55 : verifyOpen24 0 28672 = true := verifyOpen24_join' s54 v24_55 (by decide)
  have s56 : verifyOpen24 0 29184 = true := verifyOpen24_join' s55 v24_56 (by decide)
  have s57 : verifyOpen24 0 29696 = true := verifyOpen24_join' s56 v24_57 (by decide)
  have s58 : verifyOpen24 0 30208 = true := verifyOpen24_join' s57 v24_58 (by decide)
  have s59 : verifyOpen24 0 30720 = true := verifyOpen24_join' s58 v24_59 (by decide)
  have s60 : verifyOpen24 0 31232 = true := verifyOpen24_join' s59 v24_60 (by decide)
  have s61 : verifyOpen24 0 31744 = true := verifyOpen24_join' s60 v24_61 (by decide)
  have s62 : verifyOpen24 0 32256 = true := verifyOpen24_join' s61 v24_62 (by decide)
  have s63 : verifyOpen24 0 32768 = true := verifyOpen24_join' s62 v24_63 (by decide)
  have s64 : verifyOpen24 0 33280 = true := verifyOpen24_join' s63 v24_64 (by decide)
  have s65 : verifyOpen24 0 33792 = true := verifyOpen24_join' s64 v24_65 (by decide)
  have s66 : verifyOpen24 0 34304 = true := verifyOpen24_join' s65 v24_66 (by decide)
  have s67 : verifyOpen24 0 34816 = true := verifyOpen24_join' s66 v24_67 (by decide)
  have s68 : verifyOpen24 0 35328 = true := verifyOpen24_join' s67 v24_68 (by decide)
  have s69 : verifyOpen24 0 35840 = true := verifyOpen24_join' s68 v24_69 (by decide)
  have s70 : verifyOpen24 0 36352 = true := verifyOpen24_join' s69 v24_70 (by decide)
  have s71 : verifyOpen24 0 36864 = true := verifyOpen24_join' s70 v24_71 (by decide)
  have s72 : verifyOpen24 0 37376 = true := verifyOpen24_join' s71 v24_72 (by decide)
  have s73 : verifyOpen24 0 37888 = true := verifyOpen24_join' s72 v24_73 (by decide)
  have s74 : verifyOpen24 0 38400 = true := verifyOpen24_join' s73 v24_74 (by decide)
  have s75 : verifyOpen24 0 38912 = true := verifyOpen24_join' s74 v24_75 (by decide)
  have s76 : verifyOpen24 0 39424 = true := verifyOpen24_join' s75 v24_76 (by decide)
  have s77 : verifyOpen24 0 39936 = true := verifyOpen24_join' s76 v24_77 (by decide)
  have s78 : verifyOpen24 0 40448 = true := verifyOpen24_join' s77 v24_78 (by decide)
  have s79 : verifyOpen24 0 40960 = true := verifyOpen24_join' s78 v24_79 (by decide)
  have s80 : verifyOpen24 0 41472 = true := verifyOpen24_join' s79 v24_80 (by decide)
  have s81 : verifyOpen24 0 41984 = true := verifyOpen24_join' s80 v24_81 (by decide)
  have s82 : verifyOpen24 0 42496 = true := verifyOpen24_join' s81 v24_82 (by decide)
  have s83 : verifyOpen24 0 43008 = true := verifyOpen24_join' s82 v24_83 (by decide)
  have s84 : verifyOpen24 0 43520 = true := verifyOpen24_join' s83 v24_84 (by decide)
  have s85 : verifyOpen24 0 44032 = true := verifyOpen24_join' s84 v24_85 (by decide)
  have s86 : verifyOpen24 0 44544 = true := verifyOpen24_join' s85 v24_86 (by decide)
  have s87 : verifyOpen24 0 45056 = true := verifyOpen24_join' s86 v24_87 (by decide)
  have s88 : verifyOpen24 0 45568 = true := verifyOpen24_join' s87 v24_88 (by decide)
  have s89 : verifyOpen24 0 46080 = true := verifyOpen24_join' s88 v24_89 (by decide)
  have s90 : verifyOpen24 0 46592 = true := verifyOpen24_join' s89 v24_90 (by decide)
  have s91 : verifyOpen24 0 47104 = true := verifyOpen24_join' s90 v24_91 (by decide)
  have s92 : verifyOpen24 0 47616 = true := verifyOpen24_join' s91 v24_92 (by decide)
  have s93 : verifyOpen24 0 48128 = true := verifyOpen24_join' s92 v24_93 (by decide)
  have s94 : verifyOpen24 0 48640 = true := verifyOpen24_join' s93 v24_94 (by decide)
  have s95 : verifyOpen24 0 49152 = true := verifyOpen24_join' s94 v24_95 (by decide)
  have s96 : verifyOpen24 0 49664 = true := verifyOpen24_join' s95 v24_96 (by decide)
  have s97 : verifyOpen24 0 50176 = true := verifyOpen24_join' s96 v24_97 (by decide)
  have s98 : verifyOpen24 0 50688 = true := verifyOpen24_join' s97 v24_98 (by decide)
  have s99 : verifyOpen24 0 51200 = true := verifyOpen24_join' s98 v24_99 (by decide)
  have s100 : verifyOpen24 0 51712 = true := verifyOpen24_join' s99 v24_100 (by decide)
  have s101 : verifyOpen24 0 52224 = true := verifyOpen24_join' s100 v24_101 (by decide)
  have s102 : verifyOpen24 0 52736 = true := verifyOpen24_join' s101 v24_102 (by decide)
  have s103 : verifyOpen24 0 53248 = true := verifyOpen24_join' s102 v24_103 (by decide)
  have s104 : verifyOpen24 0 53760 = true := verifyOpen24_join' s103 v24_104 (by decide)
  have s105 : verifyOpen24 0 54272 = true := verifyOpen24_join' s104 v24_105 (by decide)
  have s106 : verifyOpen24 0 54784 = true := verifyOpen24_join' s105 v24_106 (by decide)
  have s107 : verifyOpen24 0 55296 = true := verifyOpen24_join' s106 v24_107 (by decide)
  have s108 : verifyOpen24 0 55808 = true := verifyOpen24_join' s107 v24_108 (by decide)
  have s109 : verifyOpen24 0 56320 = true := verifyOpen24_join' s108 v24_109 (by decide)
  have s110 : verifyOpen24 0 56832 = true := verifyOpen24_join' s109 v24_110 (by decide)
  have s111 : verifyOpen24 0 57344 = true := verifyOpen24_join' s110 v24_111 (by decide)
  have s112 : verifyOpen24 0 57856 = true := verifyOpen24_join' s111 v24_112 (by decide)
  have s113 : verifyOpen24 0 58368 = true := verifyOpen24_join' s112 v24_113 (by decide)
  have s114 : verifyOpen24 0 58880 = true := verifyOpen24_join' s113 v24_114 (by decide)
  have s115 : verifyOpen24 0 59392 = true := verifyOpen24_join' s114 v24_115 (by decide)
  have s116 : verifyOpen24 0 59904 = true := verifyOpen24_join' s115 v24_116 (by decide)
  have s117 : verifyOpen24 0 60416 = true := verifyOpen24_join' s116 v24_117 (by decide)
  have s118 : verifyOpen24 0 60928 = true := verifyOpen24_join' s117 v24_118 (by decide)
  have s119 : verifyOpen24 0 61440 = true := verifyOpen24_join' s118 v24_119 (by decide)
  have s120 : verifyOpen24 0 61952 = true := verifyOpen24_join' s119 v24_120 (by decide)
  have s121 : verifyOpen24 0 62464 = true := verifyOpen24_join' s120 v24_121 (by decide)
  have s122 : verifyOpen24 0 62976 = true := verifyOpen24_join' s121 v24_122 (by decide)
  have s123 : verifyOpen24 0 63488 = true := verifyOpen24_join' s122 v24_123 (by decide)
  have s124 : verifyOpen24 0 64000 = true := verifyOpen24_join' s123 v24_124 (by decide)
  have s125 : verifyOpen24 0 64512 = true := verifyOpen24_join' s124 v24_125 (by decide)
  have s126 : verifyOpen24 0 65024 = true := verifyOpen24_join' s125 v24_126 (by decide)
  have s127 : verifyOpen24 0 65536 = true := verifyOpen24_join' s126 v24_127 (by decide)
  exact s127

/-- **Jede Zahl `1 < m < 2^24` fällt unter sich selbst.** -/
theorem descends_below_2_24 : ∀ m, 1 < m → m < 16777216 → Descends m := by
  intro m h1 hm
  by_cases hs : m < 4194304
  · exact descends_below_2_22 m h1 hs
  · exact descends_of_verifyOpen24 verifyOpen24_all (by omega) hm

/-- **Alle Zahlen von 1 bis 2^24 − 1 = 16 777 215 erreichen die 1** (Sieb + Kernel-Rechnung). -/
theorem reachesOne_below_2_24 : ∀ n, 0 < n → n < 16777216 → ReachesOne n := by
  intro n h0 h
  exact reachesOne_of_descends_upto 16777215 (fun m h1 hm => descends_below_2_24 m h1 (by omega))
    n h0 (by omega)

/-- **Ein nichttrivialer Zyklus enthält nur Zahlen `≥ 2^24`.** -/
theorem nontrivial_cycle_ge_2_24 {n p : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : ∀ k, 16777216 ≤ iter k n := by
  intro k
  have hr : ¬ ReachesOne n := fun hr => by
    rcases periodic_reachesOne hp hr with h | h | h <;> omega
  refine Nat.le_of_not_lt (fun hk => ?_)
  exact hr (reachesOne_of_iter (reachesOne_below_2_24 _ (iter_pos h0 k) hk))

/-- Kernel-Rechnung: die Zyklus-Ungleichung schliesst für `m = 2^24` alle `1 ≤ j ≤ 12 275`
aus (für `j = 12 276` gilt sie nicht mehr; die Schranke ist mit dieser Methode scharf). -/
theorem cycleCheck_12275 : cycleCheck 16777216 12275 1 1 1 2 = true := by decide +kernel

/-- **Jeder nichttriviale Zyklus hat mindestens 12 276 ungerade Glieder.** -/
theorem cycle_odd_ge_12276 {n p : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : 12276 ≤ oddCount n p :=
  cycle_odd_gt hp h0 (nontrivial_cycle_ge_2_24 hp h0 hnt) cycleCheck_12275

set_option exponentiation.threshold 20000 in
/-- **Jeder nichttriviale Zyklus hat mindestens 31 733 Schritte**
(mindestens 12 276 ungerade und 19 457 gerade Glieder). -/
theorem cycle_length_ge_31733 {n p : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : 19457 ≤ evenCount n p ∧ 31733 ≤ p := by
  have hj := cycle_odd_ge_12276 hp h0 hnt
  have hbig := nontrivial_cycle_ge_2_24 hp h0 hnt
  obtain ⟨_, h3, _⟩ := cycle_inequalities (m := 16777216) hp h0 hbig
  have hsum := odd_add_even n p
  have h12276 : 3 ^ 12276 ≤ 3 ^ oddCount n p := Nat.pow_le_pow_right (by decide) hj
  have hpow : 2 ^ 19456 < 3 ^ 12276 := by decide +kernel
  have he : 19456 < evenCount n p := by
    have : 2 ^ 19456 < 2 ^ evenCount n p := by omega
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp this
  omega

/-- **Struktur eines Gegenbeispiels**: Erreicht `n > 0` die 1 nicht, so enthält seine Folge
ein kleinstes Glied `m ≥ 2^24`, das nie unterschritten wird und dessen Rest modulo `2^20`
eine der 27 328 offenen Restklassen ist. -/
theorem counterexample_structure24 {n : Nat} (h0 : 0 < n) (h : ¬ ReachesOne n) :
    ∃ k, 16777216 ≤ iter k n ∧ IsOrbitMin (iter k n) ∧ iter k n % 1048576 ∈ survivors20 := by
  obtain ⟨k, hk⟩ := exists_orbitMin n
  have hbig : 16777216 ≤ iter k n := by
    refine Nat.le_of_not_lt (fun hlt => ?_)
    exact h (reachesOne_of_iter (reachesOne_below_2_24 _ (iter_pos h0 k) hlt))
  exact ⟨k, hbig, hk, orbitMin_mem_survivors20 (by omega) hk⟩

end Collatz
