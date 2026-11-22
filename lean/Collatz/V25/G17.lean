import Collatz.Verified25

/-! Blöcke 34 und 35 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_34 : verifyOpen25 17408 512 = true := by decide +kernel
theorem v25_35 : verifyOpen25 17920 512 = true := by decide +kernel

end Collatz
