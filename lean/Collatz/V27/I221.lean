import Collatz.Verified27

/-! Teil 221 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_221 : verifyOpen27 28288 128 = true := by decide +kernel

end Collatz
