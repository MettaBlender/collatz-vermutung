import Collatz.Verified25

/-! Blöcke 10 und 11 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_10 : verifyOpen25 5120 512 = true := by decide +kernel
theorem v25_11 : verifyOpen25 5632 512 = true := by decide +kernel

end Collatz
