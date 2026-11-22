import Collatz.Verified24

/-! Blöcke 120 bis 123 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_120 : verifyOpen24 61440 512 = true := by decide +kernel
theorem v24_121 : verifyOpen24 61952 512 = true := by decide +kernel
theorem v24_122 : verifyOpen24 62464 512 = true := by decide +kernel
theorem v24_123 : verifyOpen24 62976 512 = true := by decide +kernel

end Collatz
