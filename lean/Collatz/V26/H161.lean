import Collatz.Verified26

/-! Teil 161 der Rechnung von 2^25 bis 2^26 (256 Klassen modulo 2^16). -/

namespace Collatz

theorem v26_161 : verifyOpen26 41216 256 = true := by decide +kernel

end Collatz
