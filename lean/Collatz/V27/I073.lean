import Collatz.Verified27

/-! Teil 73 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_73 : verifyOpen27 9344 128 = true := by decide +kernel

end Collatz
