import Collatz.Verified25

/-! Blöcke 44 und 45 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_44 : verifyOpen25 22528 512 = true := by decide +kernel
theorem v25_45 : verifyOpen25 23040 512 = true := by decide +kernel

end Collatz
