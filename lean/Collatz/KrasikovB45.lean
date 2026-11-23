import Collatz.KrasikovB40

/-! Etappe der Tabelle modulo 243, Tiefe 40 bis 45: Lean rechnet sie nach. -/

namespace Collatz

set_option maxRecDepth 100000 in
theorem segB45 : fastFrom 5 14 163 Q40 5 = Q45 := by decide +kernel

end Collatz
