import Collatz.Verified27

/-! Teil 391 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_391 : verifyOpen27 50048 128 = true := by decide +kernel

end Collatz
