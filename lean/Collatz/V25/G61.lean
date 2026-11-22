import Collatz.Verified25

/-! Blöcke 122 und 123 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_122 : verifyOpen25 62464 512 = true := by decide +kernel
theorem v25_123 : verifyOpen25 62976 512 = true := by decide +kernel

end Collatz
