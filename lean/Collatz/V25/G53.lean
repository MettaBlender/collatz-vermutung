import Collatz.Verified25

/-! Blöcke 106 und 107 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_106 : verifyOpen25 54272 512 = true := by decide +kernel
theorem v25_107 : verifyOpen25 54784 512 = true := by decide +kernel

end Collatz
