import Collatz.Verified25

/-! Blöcke 108 und 109 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_108 : verifyOpen25 55296 512 = true := by decide +kernel
theorem v25_109 : verifyOpen25 55808 512 = true := by decide +kernel

end Collatz
