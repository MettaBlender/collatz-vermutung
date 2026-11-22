import Collatz.Verified25

/-! Blöcke 66 und 67 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_66 : verifyOpen25 33792 512 = true := by decide +kernel
theorem v25_67 : verifyOpen25 34304 512 = true := by decide +kernel

end Collatz
