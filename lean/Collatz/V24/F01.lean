import Collatz.Verified24

/-! Blöcke 4 bis 7 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_4 : verifyOpen24 2048 512 = true := by decide +kernel
theorem v24_5 : verifyOpen24 2560 512 = true := by decide +kernel
theorem v24_6 : verifyOpen24 3072 512 = true := by decide +kernel
theorem v24_7 : verifyOpen24 3584 512 = true := by decide +kernel

end Collatz
