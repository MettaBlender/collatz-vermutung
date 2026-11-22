import Collatz.VerifiedHuge

/-! Blöcke 32 bis 39 der Rechnung bis 2^22 (je 1024 Restklassen modulo 2^16). -/

namespace Collatz

theorem huge32 : verifyOpen 65536 100 500 32768 1024 64 = true := by decide +kernel
theorem huge33 : verifyOpen 65536 100 500 33792 1024 64 = true := by decide +kernel
theorem huge34 : verifyOpen 65536 100 500 34816 1024 64 = true := by decide +kernel
theorem huge35 : verifyOpen 65536 100 500 35840 1024 64 = true := by decide +kernel
theorem huge36 : verifyOpen 65536 100 500 36864 1024 64 = true := by decide +kernel
theorem huge37 : verifyOpen 65536 100 500 37888 1024 64 = true := by decide +kernel
theorem huge38 : verifyOpen 65536 100 500 38912 1024 64 = true := by decide +kernel
theorem huge39 : verifyOpen 65536 100 500 39936 1024 64 = true := by decide +kernel

end Collatz
