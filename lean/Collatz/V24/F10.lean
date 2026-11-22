import Collatz.Verified24

/-! Blöcke 40 bis 43 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_40 : verifyOpen24 20480 512 = true := by decide +kernel
theorem v24_41 : verifyOpen24 20992 512 = true := by decide +kernel
theorem v24_42 : verifyOpen24 21504 512 = true := by decide +kernel
theorem v24_43 : verifyOpen24 22016 512 = true := by decide +kernel

end Collatz
