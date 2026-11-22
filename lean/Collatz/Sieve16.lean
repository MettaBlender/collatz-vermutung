import Collatz.Sieve

/-!
# Sieb modulo 2^16

Der Lean-Kernel rechnet das Sieb für alle 65 536 Restklassen modulo `2^16` nach
(dauert ca. 1–2 Minuten). Nur 2114 Restklassen (3.2 %) bleiben übrig.
-/

namespace Collatz

theorem survivors_65536_length : (survivors 65536 100).length = 2114 := by decide +kernel

/-- **Reduktion modulo 2^16**: Es genügt, den Abstieg für 2114 von 65 536 Restklassen
(3.2 %) zu zeigen. -/
theorem conjecture_of_descends_mod_65536
    (h : ∀ n, n % 65536 ∈ survivors 65536 100 → Descends n) : CollatzConjecture :=
  conjecture_of_survivors 65536 100 (by decide) h

end Collatz
