import Collatz.Verified25

/-! Blöcke 76 und 77 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_76 : verifyOpen25 38912 512 = true := by decide +kernel
theorem v25_77 : verifyOpen25 39424 512 = true := by decide +kernel

end Collatz
