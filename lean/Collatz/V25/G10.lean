import Collatz.Verified25

/-! Blöcke 20 und 21 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_20 : verifyOpen25 10240 512 = true := by decide +kernel
theorem v25_21 : verifyOpen25 10752 512 = true := by decide +kernel

end Collatz
