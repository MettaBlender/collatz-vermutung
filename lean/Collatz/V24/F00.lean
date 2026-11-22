import Collatz.Verified24

/-! Blöcke 0 bis 3 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_0 : verifyOpen24 0 512 = true := by decide +kernel
theorem v24_1 : verifyOpen24 512 512 = true := by decide +kernel
theorem v24_2 : verifyOpen24 1024 512 = true := by decide +kernel
theorem v24_3 : verifyOpen24 1536 512 = true := by decide +kernel

end Collatz
