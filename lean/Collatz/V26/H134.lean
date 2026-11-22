import Collatz.Verified26

/-! Teil 134 der Rechnung von 2^25 bis 2^26 (256 Klassen modulo 2^16). -/

namespace Collatz

theorem v26_134 : verifyOpen26 34304 256 = true := by decide +kernel

end Collatz
