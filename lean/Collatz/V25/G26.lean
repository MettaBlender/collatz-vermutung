import Collatz.Verified25

/-! Blöcke 52 und 53 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_52 : verifyOpen25 26624 512 = true := by decide +kernel
theorem v25_53 : verifyOpen25 27136 512 = true := by decide +kernel

end Collatz
