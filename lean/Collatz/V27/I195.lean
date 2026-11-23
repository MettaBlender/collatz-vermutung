import Collatz.Verified27

/-! Teil 195 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_195 : verifyOpen27 24960 128 = true := by decide +kernel

end Collatz
