import Collatz.Verified25

/-! Blöcke 28 und 29 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_28 : verifyOpen25 14336 512 = true := by decide +kernel
theorem v25_29 : verifyOpen25 14848 512 = true := by decide +kernel

end Collatz
