import Collatz.PeriodicParity
import Collatz.Dichotomy

/-!
# Satz 60: Keine Regel mit endlichem Gedächtnis sagt eine divergente Bahn voraus

Sei die Bahn von `n` unter `T` unbeschränkt. Dann gibt es für jede Gedächtnislänge `k`
und jede Startstelle `m` zwei Stellen `i, i' ≥ m`, an denen die letzten `k` Paritäten
übereinstimmen, die nächste Parität aber verschieden ist.

Anders gesagt: Keine Regel der Form „die nächste Parität hängt nur von den letzten `k`
Paritäten ab“ beschreibt eine divergente Bahn, nicht einmal ab einer späten Stelle.

Beweis: Gäbe es eine solche Regel ab `m`, dann wäre das Fenster an der Stelle `i + 1`
durch das Fenster an der Stelle `i` bestimmt. Es gibt nur `2^k` Fenster, also wiederholt
sich nach dem Schubfachprinzip ein Fenster, und von da an ist alles periodisch. Das
widerspricht Satz 58.
-/

namespace Collatz

/-- Binärcode einer Liste von Wahrheitswerten. -/
def nfmEnc : List Bool → Nat
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * nfmEnc l

theorem nfmEnc_lt : ∀ l : List Bool, nfmEnc l < 2 ^ l.length := by
  intro l
  induction l with
  | nil => simp [nfmEnc]
  | cons b l ih =>
    simp only [nfmEnc, List.length_cons, Nat.pow_succ]
    split <;> omega

theorem nfmEnc_inj : ∀ l l' : List Bool, l.length = l'.length → nfmEnc l = nfmEnc l' → l = l' := by
  intro l
  induction l with
  | nil => intro l' hl _; cases l' with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons b l ih =>
    intro l' hl he
    cases l' with
    | nil => simp at hl
    | cons b' l' =>
      simp only [List.length_cons] at hl
      simp only [nfmEnc] at he
      have hb : b = b' := by
        cases b <;> cases b' <;> simp at he ⊢ <;> omega
      subst hb
      have : nfmEnc l = nfmEnc l' := by split at he <;> omega
      rw [ih l' (by omega) this]

/-- Das Fenster der Länge `k` an der Stelle `i`. -/
abbrev nfmWin (k i n : Nat) : List Bool := parVec k (Titer i n)

theorem nfm_parVec_succ (k x : Nat) :
    parVec (k + 1) x = parVec k x ++ [nthPar k x] := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    show (x % 2 == 1) :: parVec (k + 1) (T x) = ((x % 2 == 1) :: parVec k (T x)) ++ _
    rw [ih]; rfl

/-- Das Fenster an `i + 1` ist der Rest des Fensters an `i` plus die nächste Parität. -/
theorem nfm_win_succ (k i n : Nat) :
    nfmWin (k + 1) i n = (nthPar i n) :: nfmWin k (i + 1) n ∧
    nfmWin (k + 1) i n = nfmWin k i n ++ [nthPar (i + k) n] := by
  constructor
  · show parVec (k + 1) (Titer i n) = _
    show (Titer i n % 2 == 1) :: parVec k (T (Titer i n)) = _
    have : T (Titer i n) = Titer (i + 1) n := by rw [pp_Titer_add]; rfl
    rw [this]; rfl
  · show parVec (k + 1) (Titer i n) = _
    rw [nfm_parVec_succ, pp_nthPar_Titer]

/-- **Satz 60**: Für eine unbeschränkte Bahn gibt es zu jedem `k` und `m` Stellen
`i, i' ≥ m` mit gleichem Fenster der Länge `k`, aber verschiedener nächster Parität. -/
theorem no_finite_memory {n : Nat} (hu : ∀ B, ∃ i, B < Titer i n) (k m : Nat) :
    ∃ i i', m ≤ i ∧ m ≤ i' ∧ nfmWin k i n = nfmWin k i' n ∧
      nthPar (i + k) n ≠ nthPar (i' + k) n := by
  apply Classical.byContradiction
  intro hno
  have rule : ∀ i i', m ≤ i → m ≤ i' → nfmWin k i n = nfmWin k i' n →
      nthPar (i + k) n = nthPar (i' + k) n := by
    intro i i' hi hi' hw
    apply Classical.byContradiction
    intro hne
    exact hno ⟨i, i', hi, hi', hw, hne⟩
  -- gleiche Fenster bleiben gleich
  have prop : ∀ i i', m ≤ i → m ≤ i' → nfmWin k i n = nfmWin k i' n →
      nfmWin k (i + 1) n = nfmWin k (i' + 1) n := by
    intro i i' hi hi' hw
    have h1 := nfm_win_succ k i n
    have h2 := nfm_win_succ k i' n
    have hbig : nfmWin (k + 1) i n = nfmWin (k + 1) i' n := by
      rw [h1.2, h2.2, hw, rule i i' hi hi' hw]
    rw [h1.1, h2.1] at hbig
    exact (List.cons.inj hbig).2
  -- Schubfach über die Fenster an m, m+1, …, m + 2^k
  have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  obtain ⟨a, b, hab, hb, he⟩ := pigeonhole (2 ^ k - 1) (fun t => nfmEnc (nfmWin k (m + t) n))
    (fun t _ => by
      show nfmEnc (nfmWin k (m + t) n) ≤ 2 ^ k - 1
      have := nfmEnc_lt (nfmWin k (m + t) n)
      rw [parVec_length] at this; omega)
  have hw : nfmWin k (m + a) n = nfmWin k (m + b) n :=
    nfmEnc_inj _ _ (by rw [parVec_length, parVec_length]) he
  have hall : ∀ t, nfmWin k (m + a + t) n = nfmWin k (m + b + t) n := by
    intro t
    induction t with
    | zero => exact hw
    | succ t ih => exact prop (m + a + t) (m + b + t) (by omega) (by omega) ih
  -- daraus: Paritäten periodisch ab m + a mit Periode b - a
  apply unbounded_aperiodic hu
  refine ⟨m + a, b - a, by omega, fun i hi => ?_⟩
  have h := hall (i - (m + a))
  have e1 : m + a + (i - (m + a)) = i := by omega
  have e2 : m + b + (i - (m + a)) = i + (b - a) := by omega
  rw [e1, e2] at h
  cases k with
  | zero =>
    -- Gedächtnis 0: die Regel sagt, alle Paritäten ab m sind gleich
    have := rule (i + (b - a)) i (by omega) (by omega) rfl
    simpa using this
  | succ k =>
    have h1 := (nfm_win_succ k i n).1
    have h2 := (nfm_win_succ k (i + (b - a)) n).1
    rw [h1, h2] at h
    exact ((List.cons.inj h).1).symm

end Collatz
