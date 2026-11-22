import Collatz.VerifiedHuge

/-! Blöcke 8 bis 15 der Rechnung bis 2^22 (je 1024 Restklassen modulo 2^16). -/

namespace Collatz

theorem huge8 : verifyOpen 65536 100 500 8192 1024 64 = true := by decide +kernel
theorem huge9 : verifyOpen 65536 100 500 9216 1024 64 = true := by decide +kernel
theorem huge10 : verifyOpen 65536 100 500 10240 1024 64 = true := by decide +kernel
theorem huge11 : verifyOpen 65536 100 500 11264 1024 64 = true := by decide +kernel
theorem huge12 : verifyOpen 65536 100 500 12288 1024 64 = true := by decide +kernel
theorem huge13 : verifyOpen 65536 100 500 13312 1024 64 = true := by decide +kernel
theorem huge14 : verifyOpen 65536 100 500 14336 1024 64 = true := by decide +kernel
theorem huge15 : verifyOpen 65536 100 500 15360 1024 64 = true := by decide +kernel

end Collatz
