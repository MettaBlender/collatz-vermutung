import Collatz.Verified24

/-! Blöcke 44 bis 47 der Rechnung von 2^22 bis 2^24 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v24_44 : verifyOpen24 22528 512 = true := by decide +kernel
theorem v24_45 : verifyOpen24 23040 512 = true := by decide +kernel
theorem v24_46 : verifyOpen24 23552 512 = true := by decide +kernel
theorem v24_47 : verifyOpen24 24064 512 = true := by decide +kernel

end Collatz
