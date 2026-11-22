import Collatz.Verified25

/-! Blöcke 26 und 27 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_26 : verifyOpen25 13312 512 = true := by decide +kernel
theorem v25_27 : verifyOpen25 13824 512 = true := by decide +kernel

end Collatz
