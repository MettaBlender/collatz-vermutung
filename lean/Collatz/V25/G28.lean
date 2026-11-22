import Collatz.Verified25

/-! Blöcke 56 und 57 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_56 : verifyOpen25 28672 512 = true := by decide +kernel
theorem v25_57 : verifyOpen25 29184 512 = true := by decide +kernel

end Collatz
