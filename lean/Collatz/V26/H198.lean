import Collatz.Verified26

/-! Teil 198 der Rechnung von 2^25 bis 2^26 (256 Klassen modulo 2^16). -/

namespace Collatz

theorem v26_198 : verifyOpen26 50688 256 = true := by decide +kernel

end Collatz
