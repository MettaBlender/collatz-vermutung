import Collatz.Verified25

/-! Blöcke 114 und 115 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_114 : verifyOpen25 58368 512 = true := by decide +kernel
theorem v25_115 : verifyOpen25 58880 512 = true := by decide +kernel

end Collatz
