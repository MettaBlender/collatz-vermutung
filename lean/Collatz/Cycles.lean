import Collatz.Sieve16
import Collatz.VerifiedLarge

/-!
# Zyklen und Gegenbeispiele: was ein Gegenbeispiel erfüllen müsste

Ein Gegenbeispiel zur Collatz-Vermutung wäre entweder ein **nichttrivialer Zyklus**
oder eine **divergente Folge**. Wir beweisen Einschränkungen für beide:

* Jeder Zyklus, der die 1 erreicht, ist der triviale Zyklus `1 → 4 → 2 → 1`.
* Das kleinste Element eines nichttrivialen Zyklus ist grösser als 100 000 und liegt
  in einer der 2114 offenen Restklassen modulo `2^16`.
* Eine Folge, die nie die 1 erreicht, enthält nur Zahlen grösser als 100 000.
-/

namespace Collatz

/-- Die Folge ab 1 bleibt im Zyklus `{1, 4, 2}`. -/
theorem iter_one_mem (k : Nat) : iter k 1 = 1 ∨ iter k 1 = 4 ∨ iter k 1 = 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iter_succ']
    rcases ih with h | h | h <;> rw [h] <;> decide

/-- `n` liegt auf einem Zyklus der Länge `p > 0`. -/
def Periodic (n p : Nat) : Prop := 0 < p ∧ iter p n = n

theorem iter_mul_period {n p : Nat} (h : iter p n = n) : ∀ t, iter (p * t) n = n := by
  intro t
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.mul_succ, iter_add, ih, h]

/-- **Ein Zyklus, der die 1 erreicht, ist der triviale Zyklus.** -/
theorem periodic_reachesOne {n p : Nat} (hp : Periodic n p) (h : ReachesOne n) :
    n = 1 ∨ n = 4 ∨ n = 2 := by
  obtain ⟨hp0, hpn⟩ := hp
  obtain ⟨j, hj⟩ := h
  -- n = iter (p*j) n = iter (p*j - j) (iter j n) = iter (p*j - j) 1
  have hle : j ≤ p * j := Nat.le_mul_of_pos_left j hp0
  have e : iter (p * j) n = iter (p * j - j) (iter j n) := by
    rw [← iter_add, Nat.add_sub_cancel' hle]
  rw [iter_mul_period hpn, hj] at e
  rw [e]; exact iter_one_mem _

/-- **Kein nichttrivialer Zyklus enthält eine Zahl von 1 bis 100 000.** -/
theorem no_small_cycle {n p : Nat} (hp : Periodic n p) (h0 : 0 < n) (h : n ≤ 100000) :
    n = 1 ∨ n = 4 ∨ n = 2 :=
  periodic_reachesOne hp (reachesOne_upto_100000 n h0 h)

/-- Alle Werte eines Zyklus sind wieder periodisch mit derselben Periode. -/
theorem periodic_iter {n p : Nat} (hp : Periodic n p) (k : Nat) : Periodic (iter k n) p := by
  refine ⟨hp.1, ?_⟩
  rw [← iter_add, Nat.add_comm, iter_add, hp.2]

/-- **Ein nichttrivialer Zyklus enthält nur Zahlen grösser als 100 000.** -/
theorem nontrivial_cycle_large {n p : Nat} (hp : Periodic n p) (h0 : 0 < n)
    (hnt : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : ∀ k, 100000 < iter k n := by
  intro k
  have hr : ¬ ReachesOne n := fun hr => by
    rcases periodic_reachesOne hp hr with h | h | h <;> omega
  refine Nat.lt_of_not_le (fun hk => ?_)
  exact hr (reachesOne_of_iter (reachesOne_upto_100000 _ (iter_pos h0 k) hk))

/-- **Eine Folge, die nie die 1 erreicht, enthält nur Zahlen grösser als 100 000.** -/
theorem not_reachesOne_large {n : Nat} (h0 : 0 < n) (h : ¬ ReachesOne n) :
    ∀ k, 100000 < iter k n := by
  intro k
  refine Nat.lt_of_not_le (fun hk => ?_)
  exact h (reachesOne_of_iter (reachesOne_upto_100000 _ (iter_pos h0 k) hk))

/-- `m` ist das kleinste Element seiner eigenen Folge (es fällt nie darunter). -/
def IsOrbitMin (m : Nat) : Prop := ∀ k, m ≤ iter k m

/-- **Das kleinste Element eines Gegenbeispiels liegt in einer offenen Restklasse.**
Fällt `m > 1` nie unter sich selbst, so ist `m mod 2^16` eine der 2114 Restklassen,
die das Sieb nicht erledigt. -/
theorem orbitMin_mem_survivors {m : Nat} (h1 : 1 < m) (hmin : IsOrbitMin m) :
    m % 65536 ∈ survivors 65536 100 := by
  cases hc : check 65536 (m % 65536) 100 65536 (m % 65536) with
  | true =>
    obtain ⟨k, hk⟩ := descends_of_check hc rfl h1
    exact absurd (hmin k) (by omega)
  | false => exact mem_survivors_of_not_check (Nat.mod_lt _ (by decide)) hc

/-- Jedes Gegenbeispiel hat ein kleinstes Folgenglied. -/
theorem exists_orbitMin (n : Nat) : ∃ k, IsOrbitMin (iter k n) := by
  -- Starke Induktion über den Wert v = iter k n: Fällt v noch weiter, nimm den kleineren Wert.
  have key : ∀ v, ∀ k, iter k n = v → ∃ k', IsOrbitMin (iter k' n) := by
    intro v
    induction v using Nat.strongRecOn with
    | _ v ih =>
      intro k hk
      by_cases hd : ∃ j, iter j v < v
      · obtain ⟨j, hj⟩ := hd
        exact ih _ hj (k + j) (by rw [iter_add, hk])
      · refine ⟨k, fun j => ?_⟩
        rw [hk]
        exact Nat.le_of_not_lt (fun hj => hd ⟨j, hj⟩)
  exact key n 0 rfl

/-- **Zusammenfassung**: Erreicht `n > 0` die 1 nicht, so enthält seine Folge eine Zahl
`m > 100000`, die nie unterschritten wird und deren Rest modulo 65 536 eine der 2114 offenen
Restklassen ist. -/
theorem counterexample_structure {n : Nat} (h0 : 0 < n) (h : ¬ ReachesOne n) :
    ∃ k, 100000 < iter k n ∧ IsOrbitMin (iter k n) ∧ iter k n % 65536 ∈ survivors 65536 100 := by
  obtain ⟨k, hk⟩ := exists_orbitMin n
  have hbig := not_reachesOne_large h0 h k
  exact ⟨k, hbig, hk, orbitMin_mem_survivors (by omega) hk⟩

end Collatz
