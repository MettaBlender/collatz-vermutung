import Collatz.Verified24

/-! Blöcke 36 bis 39 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_36 : verifyOpen24 18432 512 = true := by decide +kernel
theorem v24_37 : verifyOpen24 18944 512 = true := by decide +kernel
theorem v24_38 : verifyOpen24 19456 512 = true := by decide +kernel
theorem v24_39 : verifyOpen24 19968 512 = true := by decide +kernel

end Collatz
