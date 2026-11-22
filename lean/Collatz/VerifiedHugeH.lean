import Collatz.VerifiedHuge

/-! Blöcke 56 bis 63 der Rechnung bis 2^22 (je 1024 Restklassen modulo 2^16). -/

namespace Collatz

theorem huge56 : verifyOpen 65536 100 500 57344 1024 64 = true := by decide +kernel
theorem huge57 : verifyOpen 65536 100 500 58368 1024 64 = true := by decide +kernel
theorem huge58 : verifyOpen 65536 100 500 59392 1024 64 = true := by decide +kernel
theorem huge59 : verifyOpen 65536 100 500 60416 1024 64 = true := by decide +kernel
theorem huge60 : verifyOpen 65536 100 500 61440 1024 64 = true := by decide +kernel
theorem huge61 : verifyOpen 65536 100 500 62464 1024 64 = true := by decide +kernel
theorem huge62 : verifyOpen 65536 100 500 63488 1024 64 = true := by decide +kernel
theorem huge63 : verifyOpen 65536 100 500 64512 1024 64 = true := by decide +kernel

end Collatz
