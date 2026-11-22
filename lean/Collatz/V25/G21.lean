import Collatz.Verified25

/-! Blöcke 42 und 43 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_42 : verifyOpen25 21504 512 = true := by decide +kernel
theorem v25_43 : verifyOpen25 22016 512 = true := by decide +kernel

end Collatz
