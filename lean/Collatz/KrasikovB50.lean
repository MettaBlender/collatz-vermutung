import Collatz.KrasikovB45

/-! Letzte Etappe, Tiefe 45 bis 50: überall mindestens 58 525 359 050 790 615 Knoten bei `S = 163`. -/

namespace Collatz

set_option maxRecDepth 100000 in
theorem segB50 : allGe 58525359050790615 163 81 (fastFrom 5 14 163 Q45 5) = true := by decide +kernel

end Collatz
