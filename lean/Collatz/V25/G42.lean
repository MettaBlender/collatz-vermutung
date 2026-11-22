import Collatz.Verified25

/-! Blöcke 84 und 85 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_84 : verifyOpen25 43008 512 = true := by decide +kernel
theorem v25_85 : verifyOpen25 43520 512 = true := by decide +kernel

end Collatz
