import Collatz.Verified25

/-! Blöcke 48 und 49 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_48 : verifyOpen25 24576 512 = true := by decide +kernel
theorem v25_49 : verifyOpen25 25088 512 = true := by decide +kernel

end Collatz
