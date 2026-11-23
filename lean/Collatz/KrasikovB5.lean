import Collatz.KrasikovData5
import Collatz.KrasikovFast

/-! Etappe der Tabelle modulo 243, Tiefe 0 bis 5: Lean rechnet sie nach. -/

namespace Collatz

set_option maxRecDepth 100000 in
theorem segB5 : fastFrom 5 14 163 (tabQ 5 14 163 0) 5 = Q5 := by decide +kernel

end Collatz
