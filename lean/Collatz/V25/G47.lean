import Collatz.Verified25

/-! Blöcke 94 und 95 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_94 : verifyOpen25 48128 512 = true := by decide +kernel
theorem v25_95 : verifyOpen25 48640 512 = true := by decide +kernel

end Collatz
