import Collatz.VerifiedHuge

/-! Blöcke 0 bis 7 der Rechnung bis 2^22 (je 1024 Restklassen modulo 2^16). -/

namespace Collatz

theorem huge0 : verifyOpen 65536 100 500 0 1024 64 = true := by decide +kernel
theorem huge1 : verifyOpen 65536 100 500 1024 1024 64 = true := by decide +kernel
theorem huge2 : verifyOpen 65536 100 500 2048 1024 64 = true := by decide +kernel
theorem huge3 : verifyOpen 65536 100 500 3072 1024 64 = true := by decide +kernel
theorem huge4 : verifyOpen 65536 100 500 4096 1024 64 = true := by decide +kernel
theorem huge5 : verifyOpen 65536 100 500 5120 1024 64 = true := by decide +kernel
theorem huge6 : verifyOpen 65536 100 500 6144 1024 64 = true := by decide +kernel
theorem huge7 : verifyOpen 65536 100 500 7168 1024 64 = true := by decide +kernel

end Collatz
