import Collatz.Verified27

/-! Teil 100 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_100 : verifyOpen27 12800 128 = true := by decide +kernel

end Collatz
