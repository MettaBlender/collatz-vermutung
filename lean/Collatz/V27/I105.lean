import Collatz.Verified27

/-! Teil 105 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_105 : verifyOpen27 13440 128 = true := by decide +kernel

end Collatz
