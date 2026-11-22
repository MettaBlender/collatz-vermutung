import Collatz.Verified25

/-! Blöcke 86 und 87 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_86 : verifyOpen25 44032 512 = true := by decide +kernel
theorem v25_87 : verifyOpen25 44544 512 = true := by decide +kernel

end Collatz
