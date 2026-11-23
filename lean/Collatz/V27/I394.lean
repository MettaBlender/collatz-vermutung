import Collatz.Verified27

/-! Teil 394 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_394 : verifyOpen27 50432 128 = true := by decide +kernel

end Collatz
