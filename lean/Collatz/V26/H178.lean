import Collatz.Verified26

/-! Teil 178 der Rechnung von 2^25 bis 2^26 (256 Klassen modulo 2^16). -/

namespace Collatz

theorem v26_178 : verifyOpen26 45568 256 = true := by decide +kernel

end Collatz
