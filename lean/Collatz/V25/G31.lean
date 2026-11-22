import Collatz.Verified25

/-! Blöcke 62 und 63 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_62 : verifyOpen25 31744 512 = true := by decide +kernel
theorem v25_63 : verifyOpen25 32256 512 = true := by decide +kernel

end Collatz
