import Collatz.Verified27

/-! Teil 437 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_437 : verifyOpen27 55936 128 = true := by decide +kernel

end Collatz
