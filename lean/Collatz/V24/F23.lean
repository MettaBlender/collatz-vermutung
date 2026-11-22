import Collatz.Verified24

/-! Blöcke 92 bis 95 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_92 : verifyOpen24 47104 512 = true := by decide +kernel
theorem v24_93 : verifyOpen24 47616 512 = true := by decide +kernel
theorem v24_94 : verifyOpen24 48128 512 = true := by decide +kernel
theorem v24_95 : verifyOpen24 48640 512 = true := by decide +kernel

end Collatz
