import Collatz.Verified24

/-! Blöcke 52 bis 55 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_52 : verifyOpen24 26624 512 = true := by decide +kernel
theorem v24_53 : verifyOpen24 27136 512 = true := by decide +kernel
theorem v24_54 : verifyOpen24 27648 512 = true := by decide +kernel
theorem v24_55 : verifyOpen24 28160 512 = true := by decide +kernel

end Collatz
