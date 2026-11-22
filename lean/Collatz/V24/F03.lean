import Collatz.Verified24

/-! Blöcke 12 bis 15 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_12 : verifyOpen24 6144 512 = true := by decide +kernel
theorem v24_13 : verifyOpen24 6656 512 = true := by decide +kernel
theorem v24_14 : verifyOpen24 7168 512 = true := by decide +kernel
theorem v24_15 : verifyOpen24 7680 512 = true := by decide +kernel

end Collatz
