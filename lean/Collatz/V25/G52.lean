import Collatz.Verified25

/-! Blöcke 104 und 105 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_104 : verifyOpen25 53248 512 = true := by decide +kernel
theorem v25_105 : verifyOpen25 53760 512 = true := by decide +kernel

end Collatz
