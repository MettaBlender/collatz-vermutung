import Collatz.Verified25

/-! Blöcke 36 und 37 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_36 : verifyOpen25 18432 512 = true := by decide +kernel
theorem v25_37 : verifyOpen25 18944 512 = true := by decide +kernel

end Collatz
