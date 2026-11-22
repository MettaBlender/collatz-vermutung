import Collatz.VerifiedHuge

/-! Blöcke 40 bis 47 der Rechnung bis 2^22 (je 1024 Restklassen modulo 2^16). -/

namespace Collatz

theorem huge40 : verifyOpen 65536 100 500 40960 1024 64 = true := by decide +kernel
theorem huge41 : verifyOpen 65536 100 500 41984 1024 64 = true := by decide +kernel
theorem huge42 : verifyOpen 65536 100 500 43008 1024 64 = true := by decide +kernel
theorem huge43 : verifyOpen 65536 100 500 44032 1024 64 = true := by decide +kernel
theorem huge44 : verifyOpen 65536 100 500 45056 1024 64 = true := by decide +kernel
theorem huge45 : verifyOpen 65536 100 500 46080 1024 64 = true := by decide +kernel
theorem huge46 : verifyOpen 65536 100 500 47104 1024 64 = true := by decide +kernel
theorem huge47 : verifyOpen 65536 100 500 48128 1024 64 = true := by decide +kernel

end Collatz
