import Collatz.Verified25

/-! Blöcke 90 und 91 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_90 : verifyOpen25 46080 512 = true := by decide +kernel
theorem v25_91 : verifyOpen25 46592 512 = true := by decide +kernel

end Collatz
