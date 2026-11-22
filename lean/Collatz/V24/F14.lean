import Collatz.Verified24

/-! Blöcke 56 bis 59 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_56 : verifyOpen24 28672 512 = true := by decide +kernel
theorem v24_57 : verifyOpen24 29184 512 = true := by decide +kernel
theorem v24_58 : verifyOpen24 29696 512 = true := by decide +kernel
theorem v24_59 : verifyOpen24 30208 512 = true := by decide +kernel

end Collatz
