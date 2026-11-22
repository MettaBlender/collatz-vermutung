import Collatz.Verified24

/-! Blöcke 8 bis 11 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_8 : verifyOpen24 4096 512 = true := by decide +kernel
theorem v24_9 : verifyOpen24 4608 512 = true := by decide +kernel
theorem v24_10 : verifyOpen24 5120 512 = true := by decide +kernel
theorem v24_11 : verifyOpen24 5632 512 = true := by decide +kernel

end Collatz
