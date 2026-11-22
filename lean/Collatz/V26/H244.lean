import Collatz.Verified26

/-! Teil 244 der Rechnung von 2^25 bis 2^26 (256 Klassen modulo 2^16). -/

namespace Collatz

theorem v26_244 : verifyOpen26 62464 256 = true := by decide +kernel

end Collatz
