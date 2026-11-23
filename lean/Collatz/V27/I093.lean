import Collatz.Verified27

/-! Teil 93 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_93 : verifyOpen27 11904 128 = true := by decide +kernel

end Collatz
