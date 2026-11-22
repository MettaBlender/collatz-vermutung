import Collatz.Verified25

/-! Blöcke 74 und 75 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_74 : verifyOpen25 37888 512 = true := by decide +kernel
theorem v25_75 : verifyOpen25 38400 512 = true := by decide +kernel

end Collatz
