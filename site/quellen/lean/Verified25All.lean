import Collatz.V25.G00
import Collatz.V25.G01
import Collatz.V25.G02
import Collatz.V25.G03
import Collatz.V25.G04
import Collatz.V25.G05
import Collatz.V25.G06
import Collatz.V25.G07
import Collatz.V25.G08
import Collatz.V25.G09
import Collatz.V25.G10
import Collatz.V25.G11
import Collatz.V25.G12
import Collatz.V25.G13
import Collatz.V25.G14
import Collatz.V25.G15
import Collatz.V25.G16
import Collatz.V25.G17
import Collatz.V25.G18
import Collatz.V25.G19
import Collatz.V25.G20
import Collatz.V25.G21
import Collatz.V25.G22
import Collatz.V25.G23
import Collatz.V25.G24
import Collatz.V25.G25
import Collatz.V25.G26
import Collatz.V25.G27
import Collatz.V25.G28
import Collatz.V25.G29
import Collatz.V25.G30
import Collatz.V25.G31
import Collatz.V25.G32
import Collatz.V25.G33
import Collatz.V25.G34
import Collatz.V25.G35
import Collatz.V25.G36
import Collatz.V25.G37
import Collatz.V25.G38
import Collatz.V25.G39
import Collatz.V25.G40
import Collatz.V25.G41
import Collatz.V25.G42
import Collatz.V25.G43
import Collatz.V25.G44
import Collatz.V25.G45
import Collatz.V25.G46
import Collatz.V25.G47
import Collatz.V25.G48
import Collatz.V25.G49
import Collatz.V25.G50
import Collatz.V25.G51
import Collatz.V25.G52
import Collatz.V25.G53
import Collatz.V25.G54
import Collatz.V25.G55
import Collatz.V25.G56
import Collatz.V25.G57
import Collatz.V25.G58
import Collatz.V25.G59
import Collatz.V25.G60
import Collatz.V25.G61
import Collatz.V25.G62
import Collatz.V25.G63
import Collatz.Verified24All

/-!
# Folgerungen aus der Rechnung bis 2^25

* Alle Zahlen `1 ≤ n < 2^25 = 33 554 432` erreichen die 1.
* Ein nichttrivialer Zyklus enthält nur Zahlen `≥ 2^25`.
* Deshalb hätte er mindestens 14 271 ungerade und 22 619 gerade Glieder, also
  mindestens 36 890 Schritte.
-/

namespace Collatz

/-- Die 128 Blöcke zusammen: alle offenen Klassen modulo `2^20`. -/
theorem verifyOpen25_all : verifyOpen25 0 65536 = true := by
  have s0 : verifyOpen25 0 512 = true := v25_0
  have s1 : verifyOpen25 0 1024 = true := verifyOpen25_join' s0 v25_1 (by decide)
  have s2 : verifyOpen25 0 1536 = true := verifyOpen25_join' s1 v25_2 (by decide)
  have s3 : verifyOpen25 0 2048 = true := verifyOpen25_join' s2 v25_3 (by decide)
  have s4 : verifyOpen25 0 2560 = true := verifyOpen25_join' s3 v25_4 (by decide)
  have s5 : verifyOpen25 0 3072 = true := verifyOpen25_join' s4 v25_5 (by decide)
  have s6 : verifyOpen25 0 3584 = true := verifyOpen25_join' s5 v25_6 (by decide)
  have s7 : verifyOpen25 0 4096 = true := verifyOpen25_join' s6 v25_7 (by decide)
  have s8 : verifyOpen25 0 4608 = true := verifyOpen25_join' s7 v25_8 (by decide)
  have s9 : verifyOpen25 0 5120 = true := verifyOpen25_join' s8 v25_9 (by decide)
  have s10 : verifyOpen25 0 5632 = true := verifyOpen25_join' s9 v25_10 (by decide)
  have s11 : verifyOpen25 0 6144 = true := verifyOpen25_join' s10 v25_11 (by decide)
  have s12 : verifyOpen25 0 6656 = true := verifyOpen25_join' s11 v25_12 (by decide)
  have s13 : verifyOpen25 0 7168 = true := verifyOpen25_join' s12 v25_13 (by decide)
  have s14 : verifyOpen25 0 7680 = true := verifyOpen25_join' s13 v25_14 (by decide)
  have s15 : verifyOpen25 0 8192 = true := verifyOpen25_join' s14 v25_15 (by decide)
  have s16 : verifyOpen25 0 8704 = true := verifyOpen25_join' s15 v25_16 (by decide)
  have s17 : verifyOpen25 0 9216 = true := verifyOpen25_join' s16 v25_17 (by decide)
  have s18 : verifyOpen25 0 9728 = true := verifyOpen25_join' s17 v25_18 (by decide)
  have s19 : verifyOpen25 0 10240 = true := verifyOpen25_join' s18 v25_19 (by decide)
  have s20 : verifyOpen25 0 10752 = true := verifyOpen25_join' s19 v25_20 (by decide)
  have s21 : verifyOpen25 0 11264 = true := verifyOpen25_join' s20 v25_21 (by decide)
  have s22 : verifyOpen25 0 11776 = true := verifyOpen25_join' s21 v25_22 (by decide)
  have s23 : verifyOpen25 0 12288 = true := verifyOpen25_join' s22 v25_23 (by decide)
  have s24 : verifyOpen25 0 12800 = true := verifyOpen25_join' s23 v25_24 (by decide)
  have s25 : verifyOpen25 0 13312 = true := verifyOpen25_join' s24 v25_25 (by decide)
  have s26 : verifyOpen25 0 13824 = true := verifyOpen25_join' s25 v25_26 (by decide)
  have s27 : verifyOpen25 0 14336 = true := verifyOpen25_join' s26 v25_27 (by decide)
  have s28 : verifyOpen25 0 14848 = true := verifyOpen25_join' s27 v25_28 (by decide)
  have s29 : verifyOpen25 0 15360 = true := verifyOpen25_join' s28 v25_29 (by decide)
  have s30 : verifyOpen25 0 15872 = true := verifyOpen25_join' s29 v25_30 (by decide)
  have s31 : verifyOpen25 0 16384 = true := verifyOpen25_join' s30 v25_31 (by decide)
  have s32 : verifyOpen25 0 16896 = true := verifyOpen25_join' s31 v25_32 (by decide)
  have s33 : verifyOpen25 0 17408 = true := verifyOpen25_join' s32 v25_33 (by decide)
  have s34 : verifyOpen25 0 17920 = true := verifyOpen25_join' s33 v25_34 (by decide)
  have s35 : verifyOpen25 0 18432 = true := verifyOpen25_join' s34 v25_35 (by decide)
  have s36 : verifyOpen25 0 18944 = true := verifyOpen25_join' s35 v25_36 (by decide)
  have s37 : verifyOpen25 0 19456 = true := verifyOpen25_join' s36 v25_37 (by decide)
  have s38 : verifyOpen25 0 19968 = true := verifyOpen25_join' s37 v25_38 (by decide)
  have s39 : verifyOpen25 0 20480 = true := verifyOpen25_join' s38 v25_39 (by decide)
  have s40 : verifyOpen25 0 20992 = true := verifyOpen25_join' s39 v25_40 (by decide)
  have s41 : verifyOpen25 0 21504 = true := verifyOpen25_join' s40 v25_41 (by decide)
  have s42 : verifyOpen25 0 22016 = true := verifyOpen25_join' s41 v25_42 (by decide)
  have s43 : verifyOpen25 0 22528 = true := verifyOpen25_join' s42 v25_43 (by decide)
  have s44 : verifyOpen25 0 23040 = true := verifyOpen25_join' s43 v25_44 (by decide)
  have s45 : verifyOpen25 0 23552 = true := verifyOpen25_join' s44 v25_45 (by decide)
  have s46 : verifyOpen25 0 24064 = true := verifyOpen25_join' s45 v25_46 (by decide)
  have s47 : verifyOpen25 0 24576 = true := verifyOpen25_join' s46 v25_47 (by decide)
  have s48 : verifyOpen25 0 25088 = true := verifyOpen25_join' s47 v25_48 (by decide)
  have s49 : verifyOpen25 0 25600 = true := verifyOpen25_join' s48 v25_49 (by decide)
  have s50 : verifyOpen25 0 26112 = true := verifyOpen25_join' s49 v25_50 (by decide)
  have s51 : verifyOpen25 0 26624 = true := verifyOpen25_join' s50 v25_51 (by decide)
  have s52 : verifyOpen25 0 27136 = true := verifyOpen25_join' s51 v25_52 (by decide)
  have s53 : verifyOpen25 0 27648 = true := verifyOpen25_join' s52 v25_53 (by decide)
  have s54 : verifyOpen25 0 28160 = true := verifyOpen25_join' s53 v25_54 (by decide)
  have s55 : verifyOpen25 0 28672 = true := verifyOpen25_join' s54 v25_55 (by decide)
  have s56 : verifyOpen25 0 29184 = true := verifyOpen25_join' s55 v25_56 (by decide)
  have s57 : verifyOpen25 0 29696 = true := verifyOpen25_join' s56 v25_57 (by decide)
  have s58 : verifyOpen25 0 30208 = true := verifyOpen25_join' s57 v25_58 (by decide)
  have s59 : verifyOpen25 0 30720 = true := verifyOpen25_join' s58 v25_59 (by decide)
  have s60 : verifyOpen25 0 31232 = true := verifyOpen25_join' s59 v25_60 (by decide)
  have s61 : verifyOpen25 0 31744 = true := verifyOpen25_join' s60 v25_61 (by decide)
  have s62 : verifyOpen25 0 32256 = true := verifyOpen25_join' s61 v25_62 (by decide)
  have s63 : verifyOpen25 0 32768 = true := verifyOpen25_join' s62 v25_63 (by decide)
  have s64 : verifyOpen25 0 33280 = true := verifyOpen25_join' s63 v25_64 (by decide)
  have s65 : verifyOpen25 0 33792 = true := verifyOpen25_join' s64 v25_65 (by decide)
  have s66 : verifyOpen25 0 34304 = true := verifyOpen25_join' s65 v25_66 (by decide)
  have s67 : verifyOpen25 0 34816 = true := verifyOpen25_join' s66 v25_67 (by decide)
  have s68 : verifyOpen25 0 35328 = true := verifyOpen25_join' s67 v25_68 (by decide)
  have s69 : verifyOpen25 0 35840 = true := verifyOpen25_join' s68 v25_69 (by decide)
  have s70 : verifyOpen25 0 36352 = true := verifyOpen25_join' s69 v25_70 (by decide)
  have s71 : verifyOpen25 0 36864 = true := verifyOpen25_join' s70 v25_71 (by decide)
  have s72 : verifyOpen25 0 37376 = true := verifyOpen25_join' s71 v25_72 (by decide)
  have s73 : verifyOpen25 0 37888 = true := verifyOpen25_join' s72 v25_73 (by decide)
  have s74 : verifyOpen25 0 38400 = true := verifyOpen25_join' s73 v25_74 (by decide)
  have s75 : verifyOpen25 0 38912 = true := verifyOpen25_join' s74 v25_75 (by decide)
  have s76 : verifyOpen25 0 39424 = true := verifyOpen25_join' s75 v25_76 (by decide)
  have s77 : verifyOpen25 0 39936 = true := verifyOpen25_join' s76 v25_77 (by decide)
  have s78 : verifyOpen25 0 40448 = true := verifyOpen25_join' s77 v25_78 (by decide)
  have s79 : verifyOpen25 0 40960 = true := verifyOpen25_join' s78 v25_79 (by decide)
  have s80 : verifyOpen25 0 41472 = true := verifyOpen25_join' s79 v25_80 (by decide)
  have s81 : verifyOpen25 0 41984 = true := verifyOpen25_join' s80 v25_81 (by decide)
  have s82 : verifyOpen25 0 42496 = true := verifyOpen25_join' s81 v25_82 (by decide)
  have s83 : verifyOpen25 0 43008 = true := verifyOpen25_join' s82 v25_83 (by decide)
  have s84 : verifyOpen25 0 43520 = true := verifyOpen25_join' s83 v25_84 (by decide)
  have s85 : verifyOpen25 0 44032 = true := verifyOpen25_join' s84 v25_85 (by decide)
  have s86 : verifyOpen25 0 44544 = true := verifyOpen25_join' s85 v25_86 (by decide)
  have s87 : verifyOpen25 0 45056 = true := verifyOpen25_join' s86 v25_87 (by decide)
  have s88 : verifyOpen25 0 45568 = true := verifyOpen25_join' s87 v25_88 (by decide)
  have s89 : verifyOpen25 0 46080 = true := verifyOpen25_join' s88 v25_89 (by decide)
  have s90 : verifyOpen25 0 46592 = true := verifyOpen25_join' s89 v25_90 (by decide)
  have s91 : verifyOpen25 0 47104 = true := verifyOpen25_join' s90 v25_91 (by decide)
  have s92 : verifyOpen25 0 47616 = true := verifyOpen25_join' s91 v25_92 (by decide)
  have s93 : verifyOpen25 0 48128 = true := verifyOpen25_join' s92 v25_93 (by decide)
  have s94 : verifyOpen25 0 48640 = true := verifyOpen25_join' s93 v25_94 (by decide)
  have s95 : verifyOpen25 0 49152 = true := verifyOpen25_join' s94 v25_95 (by decide)
  have s96 : verifyOpen25 0 49664 = true := verifyOpen25_join' s95 v25_96 (by decide)
  have s97 : verifyOpen25 0 50176 = true := verifyOpen25_join' s96 v25_97 (by decide)
  have s98 : verifyOpen25 0 50688 = true := verifyOpen25_join' s97 v25_98 (by decide)
  have s99 : verifyOpen25 0 51200 = true := verifyOpen25_join' s98 v25_99 (by decide)
  have s100 : verifyOpen25 0 51712 = true := verifyOpen25_join' s99 v25_100 (by decide)
  have s101 : verifyOpen25 0 52224 = true := verifyOpen25_join' s100 v25_101 (by decide)
  have s102 : verifyOpen25 0 52736 = true := verifyOpen25_join' s101 v25_102 (by decide)
  have s103 : verifyOpen25 0 53248 = true := verifyOpen25_join' s102 v25_103 (by decide)
  have s104 : verifyOpen25 0 53760 = true := verifyOpen25_join' s103 v25_104 (by decide)
  have s105 : verifyOpen25 0 54272 = true := verifyOpen25_join' s104 v25_105 (by decide)
  have s106 : verifyOpen25 0 54784 = true := verifyOpen25_join' s105 v25_106 (by decide)
  have s107 : verifyOpen25 0 55296 = true := verifyOpen25_join' s106 v25_107 (by decide)
  have s108 : verifyOpen25 0 55808 = true := verifyOpen25_join' s107 v25_108 (by decide)
  have s109 : verifyOpen25 0 56320 = true := verifyOpen25_join' s108 v25_109 (by decide)
  have s110 : verifyOpen25 0 56832 = true := verifyOpen25_join' s109 v25_110 (by decide)
  have s111 : verifyOpen25 0 57344 = true := verifyOpen25_join' s110 v25_111 (by decide)
  have s112 : verifyOpen25 0 57856 = true := verifyOpen25_join' s111 v25_112 (by decide)
  have s113 : verifyOpen25 0 58368 = true := verifyOpen25_join' s112 v25_113 (by decide)
  have s114 : verifyOpen25 0 58880 = true := verifyOpen25_join' s113 v25_114 (by decide)
  have s115 : verifyOpen25 0 59392 = true := verifyOpen25_join' s114 v25_115 (by decide)
  have s116 : verifyOpen25 0 59904 = true := verifyOpen25_join' s115 v25_116 (by decide)
  have s117 : verifyOpen25 0 60416 = true := verifyOpen25_join' s116 v25_117 (by decide)
  have s118 : verifyOpen25 0 60928 = true := verifyOpen25_join' s117 v25_118 (by decide)
  have s119 : verifyOpen25 0 61440 = true := verifyOpen25_join' s118 v25_119 (by decide)
  have s120 : verifyOpen25 0 61952 = true := verifyOpen25_join' s119 v25_120 (by decide)
  have s121 : verifyOpen25 0 62464 = true := verifyOpen25_join' s120 v25_121 (by decide)
  have s122 : verifyOpen25 0 62976 = true := verifyOpen25_join' s121 v25_122 (by decide)
  have s123 : verifyOpen25 0 63488 = true := verifyOpen25_join' s122 v25_123 (by decide)
  have s124 : verifyOpen25 0 64000 = true := verifyOpen25_join' s123 v25_124 (by decide)
  have s125 : verifyOpen25 0 64512 = true := verifyOpen25_join' s124 v25_125 (by decide)
  have s126 : verifyOpen25 0 65024 = true := verifyOpen25_join' s125 v25_126 (by decide)
  have s127 : verifyOpen25 0 65536 = true := verifyOpen25_join' s126 v25_127 (by decide)
  exact s127

/-- **Jede Zahl `1 < m < 2^25` fällt unter sich selbst.** -/
theorem descends_below_2_25 : ∀ m, 1 < m → m < 33554432 → Descends m := by
  intro m h1 hm
  by_cases hs : m < 16777216
  · exact descends_below_2_24 m h1 hs
  · exact descends_of_verifyOpen25 verifyOpen25_all (by omega) hm

/-- **Alle Zahlen von 1 bis 2^25 − 1 = 33 554 431 erreichen die 1** (Sieb + Kernel-Rechnung). -/
theorem reachesOne_below_2_25 : ∀ n, 0 < n → n < 33554432 → ReachesOne n := by
  intro n h0 h
  exact reachesOne_of_descends_upto 33554431 (fun m h1 hm => descends_below_2_25 m h1 (by omega))
    n h0 (by omega)

/-- **Ein nichttrivialer Zyklus enthält nur Zahlen `≥ 2^25`.** -/
theorem nontrivial_cycle_ge_2_25 {n p : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : ∀ k, 33554432 ≤ iter k n := by
  intro k
  have hr : ¬ ReachesOne n := fun hr => by
    rcases periodic_reachesOne hp hr with h | h | h <;> omega
  refine Nat.le_of_not_lt (fun hk => ?_)
  exact hr (reachesOne_of_iter (reachesOne_below_2_25 _ (iter_pos h0 k) hk))

/-- Kernel-Rechnung: die Zyklus-Ungleichung schliesst für `m = 2^25` alle `1 ≤ j ≤ 14 270`
aus (für `j = 14 271` gilt sie nicht mehr). -/
theorem cycleCheck_14270 : cycleCheck 33554432 14270 1 1 1 2 = true := by decide +kernel

/-- **Jeder nichttriviale Zyklus hat mindestens 14 271 ungerade Glieder.** -/
theorem cycle_odd_ge_14271 {n p : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : 14271 ≤ oddCount n p :=
  cycle_odd_gt hp h0 (nontrivial_cycle_ge_2_25 hp h0 hnt) cycleCheck_14270

set_option exponentiation.threshold 30000 in
/-- **Jeder nichttriviale Zyklus hat mindestens 36 890 Schritte**
(mindestens 14 271 ungerade und 22 619 gerade Glieder). -/
theorem cycle_length_ge_36890 {n p : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : 22619 ≤ evenCount n p ∧ 36890 ≤ p := by
  have hj := cycle_odd_ge_14271 hp h0 hnt
  have hbig := nontrivial_cycle_ge_2_25 hp h0 hnt
  obtain ⟨_, h3, _⟩ := cycle_inequalities (m := 33554432) hp h0 hbig
  have hsum := odd_add_even n p
  have h14271 : 3 ^ 14271 ≤ 3 ^ oddCount n p := Nat.pow_le_pow_right (by decide) hj
  have hpow : 2 ^ 22618 < 3 ^ 14271 := by decide +kernel
  have he : 22618 < evenCount n p := by
    have : 2 ^ 22618 < 2 ^ evenCount n p := by omega
    exact (Nat.pow_lt_pow_iff_right (by decide)).mp this
  omega

/-- **Struktur eines Gegenbeispiels**: Erreicht `n > 0` die 1 nicht, so enthält seine Folge
ein kleinstes Glied `m ≥ 2^25`, das nie unterschritten wird und dessen Rest modulo `2^20`
eine der 27 328 offenen Restklassen ist. -/
theorem counterexample_structure25 {n : Nat} (h0 : 0 < n) (h : ¬ ReachesOne n) :
    ∃ k, 33554432 ≤ iter k n ∧ IsOrbitMin (iter k n) ∧ iter k n % 1048576 ∈ survivors20 := by
  obtain ⟨k, hk⟩ := exists_orbitMin n
  have hbig : 33554432 ≤ iter k n := by
    refine Nat.le_of_not_lt (fun hlt => ?_)
    exact h (reachesOne_of_iter (reachesOne_below_2_25 _ (iter_pos h0 k) hlt))
  exact ⟨k, hbig, hk, orbitMin_mem_survivors20 (by omega) hk⟩

end Collatz
