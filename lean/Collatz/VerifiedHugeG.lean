import Collatz.VerifiedHuge

/-! Blöcke 48 bis 55 der Rechnung bis 2^22 (je 1024 Restklassen modulo 2^16). -/

namespace Collatz

theorem huge48 : verifyOpen 65536 100 500 49152 1024 64 = true := by decide +kernel
theorem huge49 : verifyOpen 65536 100 500 50176 1024 64 = true := by decide +kernel
theorem huge50 : verifyOpen 65536 100 500 51200 1024 64 = true := by decide +kernel
theorem huge51 : verifyOpen 65536 100 500 52224 1024 64 = true := by decide +kernel
theorem huge52 : verifyOpen 65536 100 500 53248 1024 64 = true := by decide +kernel
theorem huge53 : verifyOpen 65536 100 500 54272 1024 64 = true := by decide +kernel
theorem huge54 : verifyOpen 65536 100 500 55296 1024 64 = true := by decide +kernel
theorem huge55 : verifyOpen 65536 100 500 56320 1024 64 = true := by decide +kernel

end Collatz
