import Collatz.Verified25

/-! Blöcke 78 und 79 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_78 : verifyOpen25 39936 512 = true := by decide +kernel
theorem v25_79 : verifyOpen25 40448 512 = true := by decide +kernel

end Collatz
