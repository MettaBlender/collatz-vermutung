import Collatz.Verified27

/-! Teil 113 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_113 : verifyOpen27 14464 128 = true := by decide +kernel

end Collatz
