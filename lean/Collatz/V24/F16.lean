import Collatz.Verified24

/-! Blöcke 64 bis 67 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_64 : verifyOpen24 32768 512 = true := by decide +kernel
theorem v24_65 : verifyOpen24 33280 512 = true := by decide +kernel
theorem v24_66 : verifyOpen24 33792 512 = true := by decide +kernel
theorem v24_67 : verifyOpen24 34304 512 = true := by decide +kernel

end Collatz
