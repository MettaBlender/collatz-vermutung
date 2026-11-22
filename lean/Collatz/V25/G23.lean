import Collatz.Verified25

/-! Blöcke 46 und 47 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_46 : verifyOpen25 23552 512 = true := by decide +kernel
theorem v25_47 : verifyOpen25 24064 512 = true := by decide +kernel

end Collatz
