import Collatz.Verified25

/-! Blöcke 102 und 103 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_102 : verifyOpen25 52224 512 = true := by decide +kernel
theorem v25_103 : verifyOpen25 52736 512 = true := by decide +kernel

end Collatz
