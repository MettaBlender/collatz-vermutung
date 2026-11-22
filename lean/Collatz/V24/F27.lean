import Collatz.Verified24

/-! Blöcke 108 bis 111 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_108 : verifyOpen24 55296 512 = true := by decide +kernel
theorem v24_109 : verifyOpen24 55808 512 = true := by decide +kernel
theorem v24_110 : verifyOpen24 56320 512 = true := by decide +kernel
theorem v24_111 : verifyOpen24 56832 512 = true := by decide +kernel

end Collatz
