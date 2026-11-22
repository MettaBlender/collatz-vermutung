import Collatz.Verified24

/-! Blöcke 104 bis 107 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_104 : verifyOpen24 53248 512 = true := by decide +kernel
theorem v24_105 : verifyOpen24 53760 512 = true := by decide +kernel
theorem v24_106 : verifyOpen24 54272 512 = true := by decide +kernel
theorem v24_107 : verifyOpen24 54784 512 = true := by decide +kernel

end Collatz
