import Collatz.Verified24

/-! Blöcke 24 bis 27 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_24 : verifyOpen24 12288 512 = true := by decide +kernel
theorem v24_25 : verifyOpen24 12800 512 = true := by decide +kernel
theorem v24_26 : verifyOpen24 13312 512 = true := by decide +kernel
theorem v24_27 : verifyOpen24 13824 512 = true := by decide +kernel

end Collatz
