import Collatz.Verified25

/-! Blöcke 8 und 9 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_8 : verifyOpen25 4096 512 = true := by decide +kernel
theorem v25_9 : verifyOpen25 4608 512 = true := by decide +kernel

end Collatz
