import Collatz.Verified27

/-! Teil 134 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_134 : verifyOpen27 17152 128 = true := by decide +kernel

end Collatz
