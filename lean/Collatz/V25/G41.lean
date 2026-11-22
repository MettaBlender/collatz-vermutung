import Collatz.Verified25

/-! Blöcke 82 und 83 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_82 : verifyOpen25 41984 512 = true := by decide +kernel
theorem v25_83 : verifyOpen25 42496 512 = true := by decide +kernel

end Collatz
