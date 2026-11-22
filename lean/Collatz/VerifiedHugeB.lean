import Collatz.VerifiedHuge

/-! Blöcke 8 bis 15 der Rechnung bis 2^22 (je 2048 Restklassen modulo 2^16). -/

namespace Collatz

theorem huge8 : verifyOpen 65536 100 500 16384 2048 64 = true := by decide +kernel
theorem huge9 : verifyOpen 65536 100 500 18432 2048 64 = true := by decide +kernel
theorem huge10 : verifyOpen 65536 100 500 20480 2048 64 = true := by decide +kernel
theorem huge11 : verifyOpen 65536 100 500 22528 2048 64 = true := by decide +kernel
theorem huge12 : verifyOpen 65536 100 500 24576 2048 64 = true := by decide +kernel
theorem huge13 : verifyOpen 65536 100 500 26624 2048 64 = true := by decide +kernel
theorem huge14 : verifyOpen 65536 100 500 28672 2048 64 = true := by decide +kernel
theorem huge15 : verifyOpen 65536 100 500 30720 2048 64 = true := by decide +kernel

end Collatz
