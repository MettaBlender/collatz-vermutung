import Collatz.Verified25

/-! Blöcke 96 und 97 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_96 : verifyOpen25 49152 512 = true := by decide +kernel
theorem v25_97 : verifyOpen25 49664 512 = true := by decide +kernel

end Collatz
