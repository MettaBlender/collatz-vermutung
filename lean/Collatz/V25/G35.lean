import Collatz.Verified25

/-! Blöcke 70 und 71 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_70 : verifyOpen25 35840 512 = true := by decide +kernel
theorem v25_71 : verifyOpen25 36352 512 = true := by decide +kernel

end Collatz
