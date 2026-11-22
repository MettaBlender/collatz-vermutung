import Collatz.Verified24

/-! Blöcke 48 bis 51 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_48 : verifyOpen24 24576 512 = true := by decide +kernel
theorem v24_49 : verifyOpen24 25088 512 = true := by decide +kernel
theorem v24_50 : verifyOpen24 25600 512 = true := by decide +kernel
theorem v24_51 : verifyOpen24 26112 512 = true := by decide +kernel

end Collatz
