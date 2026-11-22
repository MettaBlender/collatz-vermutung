import Collatz.Verified26

/-! Teil 104 der Rechnung von 2^25 bis 2^26 (256 Klassen modulo 2^16). -/

namespace Collatz

theorem v26_104 : verifyOpen26 26624 256 = true := by decide +kernel

end Collatz
