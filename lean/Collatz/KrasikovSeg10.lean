import Collatz.KrasikovSeg5

/-! Etappe der Tabelle, Tiefe 5 bis 10: Lean rechnet sie nach. -/

namespace Collatz

set_option maxRecDepth 100000 in
theorem seg10 : tabFrom 4 12 106 K5 5 = K10 := by decide +kernel

end Collatz
