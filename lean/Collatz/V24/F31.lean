import Collatz.Verified24

/-! Blöcke 124 bis 127 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_124 : verifyOpen24 63488 512 = true := by decide +kernel
theorem v24_125 : verifyOpen24 64000 512 = true := by decide +kernel
theorem v24_126 : verifyOpen24 64512 512 = true := by decide +kernel
theorem v24_127 : verifyOpen24 65024 512 = true := by decide +kernel

end Collatz
