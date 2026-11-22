import Collatz.Verified25

/-! Blöcke 118 und 119 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_118 : verifyOpen25 60416 512 = true := by decide +kernel
theorem v25_119 : verifyOpen25 60928 512 = true := by decide +kernel

end Collatz
