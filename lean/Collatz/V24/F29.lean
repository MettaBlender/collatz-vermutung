import Collatz.Verified24

/-! Blöcke 116 bis 119 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_116 : verifyOpen24 59392 512 = true := by decide +kernel
theorem v24_117 : verifyOpen24 59904 512 = true := by decide +kernel
theorem v24_118 : verifyOpen24 60416 512 = true := by decide +kernel
theorem v24_119 : verifyOpen24 60928 512 = true := by decide +kernel

end Collatz
