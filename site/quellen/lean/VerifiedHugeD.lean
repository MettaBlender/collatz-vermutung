import Collatz.VerifiedHuge

/-! Blöcke 24 bis 31 der Rechnung bis 2^22 (je 2048 Restklassen modulo 2^16). -/

namespace Collatz

theorem huge24 : verifyOpen 65536 100 500 49152 2048 64 = true := by decide +kernel
theorem huge25 : verifyOpen 65536 100 500 51200 2048 64 = true := by decide +kernel
theorem huge26 : verifyOpen 65536 100 500 53248 2048 64 = true := by decide +kernel
theorem huge27 : verifyOpen 65536 100 500 55296 2048 64 = true := by decide +kernel
theorem huge28 : verifyOpen 65536 100 500 57344 2048 64 = true := by decide +kernel
theorem huge29 : verifyOpen 65536 100 500 59392 2048 64 = true := by decide +kernel
theorem huge30 : verifyOpen 65536 100 500 61440 2048 64 = true := by decide +kernel
theorem huge31 : verifyOpen 65536 100 500 63488 2048 64 = true := by decide +kernel

end Collatz
