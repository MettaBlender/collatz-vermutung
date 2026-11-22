import Collatz.Verified25

/-! Blöcke 100 und 101 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_100 : verifyOpen25 51200 512 = true := by decide +kernel
theorem v25_101 : verifyOpen25 51712 512 = true := by decide +kernel

end Collatz
