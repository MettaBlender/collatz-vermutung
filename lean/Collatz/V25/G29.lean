import Collatz.Verified25

/-! Blöcke 58 und 59 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_58 : verifyOpen25 29696 512 = true := by decide +kernel
theorem v25_59 : verifyOpen25 30208 512 = true := by decide +kernel

end Collatz
