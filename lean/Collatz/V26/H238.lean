import Collatz.Verified26

/-! Teil 238 der Rechnung von 2^25 bis 2^26 (256 Klassen modulo 2^16). -/

namespace Collatz

theorem v26_238 : verifyOpen26 60928 256 = true := by decide +kernel

end Collatz
