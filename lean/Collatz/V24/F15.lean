import Collatz.Verified24

/-! Blöcke 60 bis 63 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_60 : verifyOpen24 30720 512 = true := by decide +kernel
theorem v24_61 : verifyOpen24 31232 512 = true := by decide +kernel
theorem v24_62 : verifyOpen24 31744 512 = true := by decide +kernel
theorem v24_63 : verifyOpen24 32256 512 = true := by decide +kernel

end Collatz
