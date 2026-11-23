import Collatz.Verified27

/-! Teil 121 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_121 : verifyOpen27 15488 128 = true := by decide +kernel

end Collatz
