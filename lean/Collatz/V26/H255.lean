import Collatz.Verified26

/-! Teil 255 der Rechnung von 2^25 bis 2^26 (256 Klassen modulo 2^16). -/

namespace Collatz

theorem v26_255 : verifyOpen26 65280 256 = true := by decide +kernel

end Collatz
