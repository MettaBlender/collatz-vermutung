import Collatz.Verified24

/-! Blöcke 68 bis 71 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_68 : verifyOpen24 34816 512 = true := by decide +kernel
theorem v24_69 : verifyOpen24 35328 512 = true := by decide +kernel
theorem v24_70 : verifyOpen24 35840 512 = true := by decide +kernel
theorem v24_71 : verifyOpen24 36352 512 = true := by decide +kernel

end Collatz
