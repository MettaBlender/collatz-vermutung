import Collatz.VerifiedHuge

/-! Blöcke 16 bis 23 der Rechnung bis 2^22 (je 2048 Restklassen modulo 2^16). -/

namespace Collatz

theorem huge16 : verifyOpen 65536 100 500 32768 2048 64 = true := by decide +kernel
theorem huge17 : verifyOpen 65536 100 500 34816 2048 64 = true := by decide +kernel
theorem huge18 : verifyOpen 65536 100 500 36864 2048 64 = true := by decide +kernel
theorem huge19 : verifyOpen 65536 100 500 38912 2048 64 = true := by decide +kernel
theorem huge20 : verifyOpen 65536 100 500 40960 2048 64 = true := by decide +kernel
theorem huge21 : verifyOpen 65536 100 500 43008 2048 64 = true := by decide +kernel
theorem huge22 : verifyOpen 65536 100 500 45056 2048 64 = true := by decide +kernel
theorem huge23 : verifyOpen 65536 100 500 47104 2048 64 = true := by decide +kernel

end Collatz
