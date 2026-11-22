import Collatz.Sieve

/-!
# Sieb modulo 2^20 durch Hochheben

Eine Restklasse `r mod 2^20`, deren Rest `r mod 2^16` schon vom Sieb erledigt ist,
muss nicht mehr geprüft werden. Wir heben deshalb nur die offenen Klassen modulo
`2^16` auf die 16 möglichen Klassen modulo `2^20` hoch und sieben dort erneut.
So prüft der Kernel etwa 65 536 + 33 824 statt 1 048 576 Restklassen.

Ergebnis: Modulo `2^20` bleiben höchstens 27 328 von 1 048 576 Restklassen (2.6 %) offen.
-/

namespace Collatz

/-- Die offenen Restklassen `r` mit `lo ≤ r < lo + len` (aufsteigend). -/
def openIn (N f : Nat) : (lo len : Nat) → List Nat
  | _, 0 => []
  | lo, len + 1 =>
    if check N lo f N lo then openIn N f (lo + 1) len else lo :: openIn N f (lo + 1) len

theorem openIn_append (N f a : Nat) :
    ∀ lo b, openIn N f lo (a + b) = openIn N f lo a ++ openIn N f (lo + a) b := by
  induction a with
  | zero => intro lo b; simp [openIn]
  | succ a ih =>
    intro lo b
    rw [Nat.add_right_comm, openIn, openIn, ih, Nat.add_assoc lo 1 a, Nat.add_comm 1 a]
    split <;> simp

theorem mem_openIn {N f r : Nat} (hc : check N r f N r = false) :
    ∀ len lo, lo ≤ r → r < lo + len → r ∈ openIn N f lo len := by
  intro len
  induction len with
  | zero => intro lo h1 h2; omega
  | succ len ih =>
    intro lo h1 h2
    unfold openIn
    by_cases hr : r = lo
    · subst hr; simp [hc]
    · have := ih (lo + 1) (by omega) (by omega)
      split <;> simp [this]

/-- Hebt jede Klasse `r mod N` aus `L` auf die `K` Klassen `r + N·j mod M` (mit `M = N·K`)
und behält nur die, die das Sieb modulo `M` nicht erledigt. -/
def lift (N M K f : Nat) (L : List Nat) : List Nat :=
  L.flatMap fun r => ((List.range K).map fun j => r + N * j).filter fun t => !check M t f M t

theorem lift_append (N M K f : Nat) (A B : List Nat) :
    lift N M K f (A ++ B) = lift N M K f A ++ lift N M K f B := by
  simp [lift, List.flatMap_append]

theorem mem_lift {N M K f r j : Nat} {L : List Nat} (hr : r ∈ L) (hj : j < K)
    (hc : check M (r + N * j) f M (r + N * j) = false) : r + N * j ∈ lift N M K f L := by
  simp only [lift, List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_range]
  exact ⟨r, hr, ⟨j, hj, rfl⟩, by simp [hc]⟩

/-- Die offenen Restklassen modulo `2^20 = 1 048 576`. -/
def survivors20 : List Nat := lift 65536 1048576 16 100 (openIn 65536 100 0 65536)

/-- **Reduktion modulo 2^20**: Es genügt, den Abstieg für die Zahlen in den offenen
Restklassen modulo `2^20` zu zeigen. -/
theorem conjecture_of_descends_mod_1048576
    (h : ∀ n, n % 1048576 ∈ survivors20 → Descends n) : CollatzConjecture := by
  apply conjecture_of_descends
  intro n h1
  cases h16 : check 65536 (n % 65536) 100 65536 (n % 65536) with
  | true => exact descends_of_check h16 rfl h1
  | false =>
    cases h20 : check 1048576 (n % 1048576) 100 1048576 (n % 1048576) with
    | true => exact descends_of_check h20 rfl h1
    | false =>
      apply h
      have ht : n % 1048576 = n % 65536 + 65536 * (n % 1048576 / 65536) := by omega
      have hm := mem_openIn h16 65536 0 (Nat.zero_le _) (by omega)
      rw [ht] at h20
      have := mem_lift (K := 16) hm (by omega) h20
      rwa [← ht] at this

/-! ## Zählen in 16 Blöcken (Blöcke in Sieve20A bis Sieve20D) -/

/-- Anzahl offener Klassen modulo 2^20 über den Klassen `lo ≤ r < lo + 4096` modulo 2^16. -/
abbrev d20 (lo : Nat) : Nat := (lift 65536 1048576 16 100 (openIn 65536 100 lo 4096)).length

abbrev D20 (len : Nat) : Nat := (lift 65536 1048576 16 100 (openIn 65536 100 0 len)).length

theorem D20_split (k : Nat) : D20 (k + 4096) = D20 k + d20 k := by
  unfold D20 d20
  rw [openIn_append, lift_append, List.length_append, Nat.zero_add]

end Collatz
