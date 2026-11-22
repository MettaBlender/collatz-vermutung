import Collatz.Verified25

/-! Blöcke 92 und 93 der Rechnung von 2^24 bis 2^25 (je 512 Klassen modulo 2^16). -/

namespace Collatz

theorem v25_92 : verifyOpen25 47104 512 = true := by decide +kernel
theorem v25_93 : verifyOpen25 47616 512 = true := by decide +kernel

end Collatz
