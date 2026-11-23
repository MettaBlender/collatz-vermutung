import Collatz.KrasikovB35

/-! Etappe der Tabelle modulo 243, Tiefe 35 bis 40: Lean rechnet sie nach. -/

namespace Collatz

set_option maxRecDepth 100000 in
theorem segB40 : fastFrom 5 14 163 Q35 5 = Q40 := by decide +kernel

end Collatz
