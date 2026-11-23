import Collatz.Verified27

/-! Teil 369 der Rechnung von 2^26 bis 2^27 (128 Klassen modulo 2^16). -/

namespace Collatz

theorem v27_369 : verifyOpen27 47232 128 = true := by decide +kernel

end Collatz
