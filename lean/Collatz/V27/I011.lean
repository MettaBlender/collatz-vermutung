import Collatz.Verified27

/-! Teil 11 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_11 : verifyOpen27 1408 128 = true := by decide +kernel

end Collatz
