import Collatz.Verified25

/-! Blöcke 110 und 111 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_110 : verifyOpen25 56320 512 = true := by decide +kernel
theorem v25_111 : verifyOpen25 56832 512 = true := by decide +kernel

end Collatz
