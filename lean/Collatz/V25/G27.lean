import Collatz.Verified25

/-! Blöcke 54 und 55 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_54 : verifyOpen25 27648 512 = true := by decide +kernel
theorem v25_55 : verifyOpen25 28160 512 = true := by decide +kernel

end Collatz
