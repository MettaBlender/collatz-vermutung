import Collatz.KrasikovData

/-! Letzte Etappe, Tiefe 25 bis 30: überall mindestens 42 319 894 058 Knoten bei `S = 106`. -/

namespace Collatz

set_option maxRecDepth 100000 in
theorem seg30 : ∀ t, t < 27 → t % 3 ≠ 0 → 42319894058 ≤ getT (tabFrom 4 12 106 K25 5) t 106 := by
  decide +kernel

end Collatz
