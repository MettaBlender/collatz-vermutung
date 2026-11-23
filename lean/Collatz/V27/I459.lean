import Collatz.Verified27

/-! Teil 459 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_459 : verifyOpen27 58752 128 = true := by decide +kernel

end Collatz
