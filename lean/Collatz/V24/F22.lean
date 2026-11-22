import Collatz.Verified24

/-! Blöcke 88 bis 91 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_88 : verifyOpen24 45056 512 = true := by decide +kernel
theorem v24_89 : verifyOpen24 45568 512 = true := by decide +kernel
theorem v24_90 : verifyOpen24 46080 512 = true := by decide +kernel
theorem v24_91 : verifyOpen24 46592 512 = true := by decide +kernel

end Collatz
