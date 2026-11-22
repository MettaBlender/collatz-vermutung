import Collatz.Verified24

/-! Blöcke 20 bis 23 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_20 : verifyOpen24 10240 512 = true := by decide +kernel
theorem v24_21 : verifyOpen24 10752 512 = true := by decide +kernel
theorem v24_22 : verifyOpen24 11264 512 = true := by decide +kernel
theorem v24_23 : verifyOpen24 11776 512 = true := by decide +kernel

end Collatz
