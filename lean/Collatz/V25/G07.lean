import Collatz.Verified25

/-! Blöcke 14 und 15 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_14 : verifyOpen25 7168 512 = true := by decide +kernel
theorem v25_15 : verifyOpen25 7680 512 = true := by decide +kernel

end Collatz
