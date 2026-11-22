import Collatz.Verified24

/-! Blöcke 96 bis 99 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_96 : verifyOpen24 49152 512 = true := by decide +kernel
theorem v24_97 : verifyOpen24 49664 512 = true := by decide +kernel
theorem v24_98 : verifyOpen24 50176 512 = true := by decide +kernel
theorem v24_99 : verifyOpen24 50688 512 = true := by decide +kernel

end Collatz
