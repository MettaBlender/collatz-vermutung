import Collatz.Verified25

/-! Blöcke 72 und 73 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_72 : verifyOpen25 36864 512 = true := by decide +kernel
theorem v25_73 : verifyOpen25 37376 512 = true := by decide +kernel

end Collatz
