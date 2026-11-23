import Collatz.Verified27

/-! Teil 265 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_265 : verifyOpen27 33920 128 = true := by decide +kernel

end Collatz
