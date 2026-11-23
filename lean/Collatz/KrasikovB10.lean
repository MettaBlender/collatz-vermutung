import Collatz.KrasikovB5

/-! Etappe der Tabelle modulo 243, Tiefe 5 bis 10: Lean rechnet sie nach. -/

namespace Collatz

set_option maxRecDepth 100000 in
theorem segB10 : fastFrom 5 14 163 Q5 5 = Q10 := by decide +kernel

end Collatz
