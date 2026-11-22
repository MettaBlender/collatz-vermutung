import Collatz.Verified25

/-! Blöcke 98 und 99 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_98 : verifyOpen25 50176 512 = true := by decide +kernel
theorem v25_99 : verifyOpen25 50688 512 = true := by decide +kernel

end Collatz
