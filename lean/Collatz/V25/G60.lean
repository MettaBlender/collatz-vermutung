import Collatz.Verified25

/-! Blöcke 120 und 121 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_120 : verifyOpen25 61440 512 = true := by decide +kernel
theorem v25_121 : verifyOpen25 61952 512 = true := by decide +kernel

end Collatz
