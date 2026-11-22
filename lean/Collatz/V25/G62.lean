import Collatz.Verified25

/-! Blöcke 124 und 125 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_124 : verifyOpen25 63488 512 = true := by decide +kernel
theorem v25_125 : verifyOpen25 64000 512 = true := by decide +kernel

end Collatz
