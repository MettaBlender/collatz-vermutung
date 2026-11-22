import Collatz.Sieve

/-!
# Sieb modulo 2^16

Wir zählen, wie viele der 65 536 Restklassen modulo `2^16` das Sieb **nicht**
erledigt. Damit der Lean-Kernel nicht zu viel Speicher braucht, wird in 16 Blöcken
zu je 4096 Restklassen gezählt und danach addiert.
Ergebnis: nur 2114 Restklassen (3.2 %) bleiben offen.
-/

namespace Collatz

/-- Anzahl offener Restklassen `r` mit `lo ≤ r < lo + len`. -/
def countOpen (N f lo : Nat) : (len : Nat) → Nat
  | 0 => 0
  | len + 1 => countOpen N f lo len + (if check N (lo + len) f N (lo + len) then 0 else 1)

theorem countOpen_add (N f lo a : Nat) :
    ∀ b, countOpen N f lo (a + b) = countOpen N f lo a + countOpen N f (lo + a) b := by
  intro b
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [← Nat.add_assoc, countOpen, ih, countOpen, Nat.add_assoc, Nat.add_assoc lo a b]

/-- `survivorsBelow` und `countOpen` zählen dasselbe. -/
theorem length_survivorsBelow (N f : Nat) :
    ∀ k, (survivorsBelow N f k).length = countOpen N f 0 k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold survivorsBelow countOpen
    rw [Nat.zero_add]
    split <;> simp [ih]

private abbrev c (lo : Nat) : Nat := countOpen 65536 100 lo 4096

theorem c0 : c 0 = 133 := by decide +kernel
theorem c1 : c 4096 = 129 := by decide +kernel
theorem c2 : c 8192 = 139 := by decide +kernel
theorem c3 : c 12288 = 127 := by decide +kernel
theorem c4 : c 16384 = 137 := by decide +kernel
theorem c5 : c 20480 = 128 := by decide +kernel
theorem c6 : c 24576 = 130 := by decide +kernel
theorem c7 : c 28672 = 135 := by decide +kernel
theorem c8 : c 32768 = 129 := by decide +kernel
theorem c9 : c 36864 = 133 := by decide +kernel
theorem c10 : c 40960 = 132 := by decide +kernel
theorem c11 : c 45056 = 133 := by decide +kernel
theorem c12 : c 49152 = 135 := by decide +kernel
theorem c13 : c 53248 = 130 := by decide +kernel
theorem c14 : c 57344 = 134 := by decide +kernel
theorem c15 : c 61440 = 130 := by decide +kernel

theorem countOpen_split (k : Nat) :
    countOpen 65536 100 0 (k + 4096) = countOpen 65536 100 0 k + c k := by
  rw [countOpen_add, Nat.zero_add]

/-- **Modulo 2^16 bleiben genau 2114 von 65 536 Restklassen offen (3.2 %).** -/
theorem survivors_65536_length : (survivors 65536 100).length = 2114 := by
  rw [survivors, List.length_reverse, length_survivorsBelow]
  have e0 : countOpen 65536 100 0 4096 = c 0 := rfl
  have e1 : countOpen 65536 100 0 8192 = _ := countOpen_split 4096
  have e2 : countOpen 65536 100 0 12288 = _ := countOpen_split 8192
  have e3 : countOpen 65536 100 0 16384 = _ := countOpen_split 12288
  have e4 : countOpen 65536 100 0 20480 = _ := countOpen_split 16384
  have e5 : countOpen 65536 100 0 24576 = _ := countOpen_split 20480
  have e6 : countOpen 65536 100 0 28672 = _ := countOpen_split 24576
  have e7 : countOpen 65536 100 0 32768 = _ := countOpen_split 28672
  have e8 : countOpen 65536 100 0 36864 = _ := countOpen_split 32768
  have e9 : countOpen 65536 100 0 40960 = _ := countOpen_split 36864
  have e10 : countOpen 65536 100 0 45056 = _ := countOpen_split 40960
  have e11 : countOpen 65536 100 0 49152 = _ := countOpen_split 45056
  have e12 : countOpen 65536 100 0 53248 = _ := countOpen_split 49152
  have e13 : countOpen 65536 100 0 57344 = _ := countOpen_split 53248
  have e14 : countOpen 65536 100 0 61440 = _ := countOpen_split 57344
  have e15 : countOpen 65536 100 0 65536 = _ := countOpen_split 61440
  rw [e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15]

/-- **Reduktion modulo 2^16**: Es genügt, den Abstieg für die 2114 offenen von
65 536 Restklassen (3.2 %) zu zeigen. -/
theorem conjecture_of_descends_mod_65536
    (h : ∀ n, n % 65536 ∈ survivors 65536 100 → Descends n) : CollatzConjecture :=
  conjecture_of_survivors 65536 100 (by decide) h

end Collatz
