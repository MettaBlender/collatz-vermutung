import Collatz.Verified27

/-! Teil 251 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_251 : verifyOpen27 32128 128 = true := by decide +kernel

end Collatz
