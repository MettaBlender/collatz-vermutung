import Collatz.Verified25

/-! Blöcke 50 und 51 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_50 : verifyOpen25 25600 512 = true := by decide +kernel
theorem v25_51 : verifyOpen25 26112 512 = true := by decide +kernel

end Collatz
