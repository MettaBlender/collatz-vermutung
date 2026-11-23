import Collatz.Verified27

/-! Teil 401 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_401 : verifyOpen27 51328 128 = true := by decide +kernel

end Collatz
