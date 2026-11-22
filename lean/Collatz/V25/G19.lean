import Collatz.Verified25

/-! Blöcke 38 und 39 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_38 : verifyOpen25 19456 512 = true := by decide +kernel
theorem v25_39 : verifyOpen25 19968 512 = true := by decide +kernel

end Collatz
