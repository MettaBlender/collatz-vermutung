import Collatz.Verified25

/-! Blöcke 68 und 69 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_68 : verifyOpen25 34816 512 = true := by decide +kernel
theorem v25_69 : verifyOpen25 35328 512 = true := by decide +kernel

end Collatz
