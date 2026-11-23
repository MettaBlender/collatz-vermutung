import Collatz.KrasikovB30

/-! Etappe der Tabelle modulo 243, Tiefe 30 bis 35: Lean rechnet sie nach. -/

namespace Collatz

set_option maxRecDepth 100000 in
theorem segB35 : fastFrom 5 14 163 Q30 5 = Q35 := by decide +kernel

end Collatz
