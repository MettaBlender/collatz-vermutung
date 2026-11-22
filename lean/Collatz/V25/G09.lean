import Collatz.Verified25

/-! Blöcke 18 und 19 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_18 : verifyOpen25 9216 512 = true := by decide +kernel
theorem v25_19 : verifyOpen25 9728 512 = true := by decide +kernel

end Collatz
