import Collatz.Verified26

/-! Teil 202 der Rechnung von 2^25 bis 2^26 (256 Klassen modulo 2^16). -/

namespace Collatz

theorem v26_202 : verifyOpen26 51712 256 = true := by decide +kernel

end Collatz
