import Collatz.Verified25

/-! Blöcke 2 und 3 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_2 : verifyOpen25 1024 512 = true := by decide +kernel
theorem v25_3 : verifyOpen25 1536 512 = true := by decide +kernel

end Collatz
