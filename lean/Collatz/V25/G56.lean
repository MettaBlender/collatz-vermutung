import Collatz.Verified25

/-! Blöcke 112 und 113 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_112 : verifyOpen25 57344 512 = true := by decide +kernel
theorem v25_113 : verifyOpen25 57856 512 = true := by decide +kernel

end Collatz
