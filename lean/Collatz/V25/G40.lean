import Collatz.Verified25

/-! Blöcke 80 und 81 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_80 : verifyOpen25 40960 512 = true := by decide +kernel
theorem v25_81 : verifyOpen25 41472 512 = true := by decide +kernel

end Collatz
