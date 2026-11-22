import Collatz.Verified26

/-! Teil 58 der Rechnung von 2^25 bis 2^26 (256 Klassen modulo 2^16). -/

namespace Collatz

theorem v26_58 : verifyOpen26 14848 256 = true := by decide +kernel

end Collatz
