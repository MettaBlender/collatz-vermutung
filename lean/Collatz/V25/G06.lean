import Collatz.Verified25

/-! Blöcke 12 und 13 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_12 : verifyOpen25 6144 512 = true := by decide +kernel
theorem v25_13 : verifyOpen25 6656 512 = true := by decide +kernel

end Collatz
