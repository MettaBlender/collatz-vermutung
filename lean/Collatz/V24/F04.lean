import Collatz.Verified24

/-! Blöcke 16 bis 19 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_16 : verifyOpen24 8192 512 = true := by decide +kernel
theorem v24_17 : verifyOpen24 8704 512 = true := by decide +kernel
theorem v24_18 : verifyOpen24 9216 512 = true := by decide +kernel
theorem v24_19 : verifyOpen24 9728 512 = true := by decide +kernel

end Collatz
