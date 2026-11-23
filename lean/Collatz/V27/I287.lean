import Collatz.Verified27

/-! Teil 287 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_287 : verifyOpen27 36736 128 = true := by decide +kernel

end Collatz
