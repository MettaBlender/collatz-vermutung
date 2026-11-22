import Collatz.Verified24

/-! Blöcke 76 bis 79 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_76 : verifyOpen24 38912 512 = true := by decide +kernel
theorem v24_77 : verifyOpen24 39424 512 = true := by decide +kernel
theorem v24_78 : verifyOpen24 39936 512 = true := by decide +kernel
theorem v24_79 : verifyOpen24 40448 512 = true := by decide +kernel

end Collatz
