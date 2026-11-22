import Collatz.Verified26

/-! Teil 75 der Rechnung von 2^25 bis 2^26 (256 Klassen modulo 2^16). -/

namespace Collatz

theorem v26_75 : verifyOpen26 19200 256 = true := by decide +kernel

end Collatz
