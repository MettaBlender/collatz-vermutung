import Collatz.Verified24

/-! Blöcke 100 bis 103 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_100 : verifyOpen24 51200 512 = true := by decide +kernel
theorem v24_101 : verifyOpen24 51712 512 = true := by decide +kernel
theorem v24_102 : verifyOpen24 52224 512 = true := by decide +kernel
theorem v24_103 : verifyOpen24 52736 512 = true := by decide +kernel

end Collatz
