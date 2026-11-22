import Collatz.Verified24

/-! Blöcke 84 bis 87 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_84 : verifyOpen24 43008 512 = true := by decide +kernel
theorem v24_85 : verifyOpen24 43520 512 = true := by decide +kernel
theorem v24_86 : verifyOpen24 44032 512 = true := by decide +kernel
theorem v24_87 : verifyOpen24 44544 512 = true := by decide +kernel

end Collatz
