import Collatz.Verified25

/-! Blöcke 16 und 17 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_16 : verifyOpen25 8192 512 = true := by decide +kernel
theorem v25_17 : verifyOpen25 8704 512 = true := by decide +kernel

end Collatz
