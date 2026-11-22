import Collatz.Verified25

/-! Blöcke 6 und 7 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_6 : verifyOpen25 3072 512 = true := by decide +kernel
theorem v25_7 : verifyOpen25 3584 512 = true := by decide +kernel

end Collatz
