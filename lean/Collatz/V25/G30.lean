import Collatz.Verified25

/-! Blöcke 60 und 61 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_60 : verifyOpen25 30720 512 = true := by decide +kernel
theorem v25_61 : verifyOpen25 31232 512 = true := by decide +kernel

end Collatz
