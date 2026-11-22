import Collatz.VerifiedHuge

/-! Blöcke 16 bis 23 der Rechnung bis 2^22 (je 1024 Restklassen modulo 2^16). -/

namespace Collatz

theorem huge16 : verifyOpen 65536 100 500 16384 1024 64 = true := by decide +kernel
theorem huge17 : verifyOpen 65536 100 500 17408 1024 64 = true := by decide +kernel
theorem huge18 : verifyOpen 65536 100 500 18432 1024 64 = true := by decide +kernel
theorem huge19 : verifyOpen 65536 100 500 19456 1024 64 = true := by decide +kernel
theorem huge20 : verifyOpen 65536 100 500 20480 1024 64 = true := by decide +kernel
theorem huge21 : verifyOpen 65536 100 500 21504 1024 64 = true := by decide +kernel
theorem huge22 : verifyOpen 65536 100 500 22528 1024 64 = true := by decide +kernel
theorem huge23 : verifyOpen 65536 100 500 23552 1024 64 = true := by decide +kernel

end Collatz
