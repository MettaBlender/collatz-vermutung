import Collatz.Verified25

/-! Blöcke 24 und 25 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_24 : verifyOpen25 12288 512 = true := by decide +kernel
theorem v25_25 : verifyOpen25 12800 512 = true := by decide +kernel

end Collatz
