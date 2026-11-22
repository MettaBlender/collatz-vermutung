import Collatz.Verified25

/-! Blöcke 116 und 117 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_116 : verifyOpen25 59392 512 = true := by decide +kernel
theorem v25_117 : verifyOpen25 59904 512 = true := by decide +kernel

end Collatz
