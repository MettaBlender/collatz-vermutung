import Collatz.Verified25

/-! Blöcke 88 und 89 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_88 : verifyOpen25 45056 512 = true := by decide +kernel
theorem v25_89 : verifyOpen25 45568 512 = true := by decide +kernel

end Collatz
