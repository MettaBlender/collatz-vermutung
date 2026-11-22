import Collatz.Verified25

/-! Blöcke 40 und 41 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_40 : verifyOpen25 20480 512 = true := by decide +kernel
theorem v25_41 : verifyOpen25 20992 512 = true := by decide +kernel

end Collatz
