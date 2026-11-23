import Collatz.Verified27

/-! Teil 352 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_352 : verifyOpen27 45056 128 = true := by decide +kernel

end Collatz
