import Collatz.Verified25

/-! Blöcke 126 und 127 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_126 : verifyOpen25 64512 512 = true := by decide +kernel
theorem v25_127 : verifyOpen25 65024 512 = true := by decide +kernel

end Collatz
