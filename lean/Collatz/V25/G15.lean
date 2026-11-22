import Collatz.Verified25

/-! Blöcke 30 und 31 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_30 : verifyOpen25 15360 512 = true := by decide +kernel
theorem v25_31 : verifyOpen25 15872 512 = true := by decide +kernel

end Collatz
