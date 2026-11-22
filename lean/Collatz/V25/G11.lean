import Collatz.Verified25

/-! Blöcke 22 und 23 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_22 : verifyOpen25 11264 512 = true := by decide +kernel
theorem v25_23 : verifyOpen25 11776 512 = true := by decide +kernel

end Collatz
