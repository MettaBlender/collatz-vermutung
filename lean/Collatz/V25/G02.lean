import Collatz.Verified25

/-! Blöcke 4 und 5 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_4 : verifyOpen25 2048 512 = true := by decide +kernel
theorem v25_5 : verifyOpen25 2560 512 = true := by decide +kernel

end Collatz
