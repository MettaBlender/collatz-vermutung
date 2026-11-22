import Collatz.Verified24

/-! Blöcke 28 bis 31 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_28 : verifyOpen24 14336 512 = true := by decide +kernel
theorem v24_29 : verifyOpen24 14848 512 = true := by decide +kernel
theorem v24_30 : verifyOpen24 15360 512 = true := by decide +kernel
theorem v24_31 : verifyOpen24 15872 512 = true := by decide +kernel

end Collatz
