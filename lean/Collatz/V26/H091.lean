import Collatz.Verified26

/-! Teil 91 der Rechnung von 2^25 bis 2^26 (256 Klassen modulo 2^16). -/

namespace Collatz

theorem v26_91 : verifyOpen26 23296 256 = true := by decide +kernel

end Collatz
