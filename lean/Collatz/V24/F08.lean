import Collatz.Verified24

/-! Blöcke 32 bis 35 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_32 : verifyOpen24 16384 512 = true := by decide +kernel
theorem v24_33 : verifyOpen24 16896 512 = true := by decide +kernel
theorem v24_34 : verifyOpen24 17408 512 = true := by decide +kernel
theorem v24_35 : verifyOpen24 17920 512 = true := by decide +kernel

end Collatz
