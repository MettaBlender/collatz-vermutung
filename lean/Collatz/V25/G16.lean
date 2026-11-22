import Collatz.Verified25

/-! Blöcke 32 und 33 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_32 : verifyOpen25 16384 512 = true := by decide +kernel
theorem v25_33 : verifyOpen25 16896 512 = true := by decide +kernel

end Collatz
