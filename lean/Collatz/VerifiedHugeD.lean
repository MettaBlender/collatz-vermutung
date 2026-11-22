import Collatz.VerifiedHuge

/-! Blöcke 24 bis 31 der Rechnung bis 2^22 (je 1024 Restklassen modulo 2^16). -/

namespace Collatz

theorem huge24 : verifyOpen 65536 100 500 24576 1024 64 = true := by decide +kernel
theorem huge25 : verifyOpen 65536 100 500 25600 1024 64 = true := by decide +kernel
theorem huge26 : verifyOpen 65536 100 500 26624 1024 64 = true := by decide +kernel
theorem huge27 : verifyOpen 65536 100 500 27648 1024 64 = true := by decide +kernel
theorem huge28 : verifyOpen 65536 100 500 28672 1024 64 = true := by decide +kernel
theorem huge29 : verifyOpen 65536 100 500 29696 1024 64 = true := by decide +kernel
theorem huge30 : verifyOpen 65536 100 500 30720 1024 64 = true := by decide +kernel
theorem huge31 : verifyOpen 65536 100 500 31744 1024 64 = true := by decide +kernel

end Collatz
