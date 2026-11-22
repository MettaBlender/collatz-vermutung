import Collatz.Verified24

/-! Blöcke 80 bis 83 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_80 : verifyOpen24 40960 512 = true := by decide +kernel
theorem v24_81 : verifyOpen24 41472 512 = true := by decide +kernel
theorem v24_82 : verifyOpen24 41984 512 = true := by decide +kernel
theorem v24_83 : verifyOpen24 42496 512 = true := by decide +kernel

end Collatz
