import Collatz.Verified24

/-! Blöcke 72 bis 75 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_72 : verifyOpen24 36864 512 = true := by decide +kernel
theorem v24_73 : verifyOpen24 37376 512 = true := by decide +kernel
theorem v24_74 : verifyOpen24 37888 512 = true := by decide +kernel
theorem v24_75 : verifyOpen24 38400 512 = true := by decide +kernel

end Collatz
