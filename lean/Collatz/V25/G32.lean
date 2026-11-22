import Collatz.Verified25

/-! Blöcke 64 und 65 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_64 : verifyOpen25 32768 512 = true := by decide +kernel
theorem v25_65 : verifyOpen25 33280 512 = true := by decide +kernel

end Collatz
