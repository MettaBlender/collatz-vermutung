import Collatz.Verified24

/-! Blöcke 112 bis 115 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_112 : verifyOpen24 57344 512 = true := by decide +kernel
theorem v24_113 : verifyOpen24 57856 512 = true := by decide +kernel
theorem v24_114 : verifyOpen24 58368 512 = true := by decide +kernel
theorem v24_115 : verifyOpen24 58880 512 = true := by decide +kernel

end Collatz
