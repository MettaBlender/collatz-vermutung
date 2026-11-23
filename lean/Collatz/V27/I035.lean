import Collatz.Verified27

/-! Teil 35 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_35 : verifyOpen27 4480 128 = true := by decide +kernel

end Collatz
