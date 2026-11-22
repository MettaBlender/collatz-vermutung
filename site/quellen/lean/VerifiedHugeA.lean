import Collatz.VerifiedHuge

/-! Blöcke 0 bis 7 der Rechnung bis 2^22 (je 2048 Restklassen modulo 2^16). -/

namespace Collatz

theorem huge0 : verifyOpen 65536 100 500 0 2048 64 = true := by decide +kernel
theorem huge1 : verifyOpen 65536 100 500 2048 2048 64 = true := by decide +kernel
theorem huge2 : verifyOpen 65536 100 500 4096 2048 64 = true := by decide +kernel
theorem huge3 : verifyOpen 65536 100 500 6144 2048 64 = true := by decide +kernel
theorem huge4 : verifyOpen 65536 100 500 8192 2048 64 = true := by decide +kernel
theorem huge5 : verifyOpen 65536 100 500 10240 2048 64 = true := by decide +kernel
theorem huge6 : verifyOpen 65536 100 500 12288 2048 64 = true := by decide +kernel
theorem huge7 : verifyOpen 65536 100 500 14336 2048 64 = true := by decide +kernel

end Collatz
