import Collatz.Krasikov

/-!
# Schnellere Tabellenrechnung für Satz 47

`nextT` schlägt für jeden Eintrag `(t, S)` die Werte `getT tab c (S − E)` einzeln nach; jedes
Nachschlagen in einer Liste kostet `O(S)` Schritte. `fastNext` rechnet stattdessen ganze Zeilen:
die Zeile von `c` um `E` nach rechts verschoben (`kShift`), elementweise addiert (`kAdd`) und das
Minimum über die drei Hebungen elementweise (`kMinL`). Das Ergebnis ist **dieselbe Liste**
(`fastNext_eq`), der Kernel braucht dafür aber etwa hundertmal weniger Schritte.
-/

namespace Collatz

def kAdd : List Nat → List Nat → List Nat
  | [], l => l
  | a :: x, [] => a :: x
  | a :: x, b :: y => (a + b) :: kAdd x y

def kMinL : List Nat → List Nat → List Nat
  | a :: x, b :: y => min a b :: kMinL x y
  | _, _ => []

def kShift (E : Nat) (row : List Nat) : List Nat := List.replicate E 0 ++ row

def kPad : Nat → List Nat → List Nat
  | 0, _ => []
  | n + 1, [] => 0 :: kPad n []
  | n + 1, a :: l => a :: kPad n l

theorem getD_nil0 (i : Nat) : ([] : List Nat).getD i 0 = 0 := by
  cases i <;> rfl

theorem getD_cons0 (a : Nat) (l : List Nat) (i : Nat) :
    (a :: l).getD (i + 1) 0 = l.getD i 0 := rfl

theorem kAdd_getD : ∀ (x y : List Nat) (i : Nat),
    (kAdd x y).getD i 0 = x.getD i 0 + y.getD i 0
  | [], l, i => by simp only [kAdd, getD_nil0, Nat.zero_add]
  | a :: x, [], i => by simp only [kAdd, getD_nil0, Nat.add_zero]
  | a :: x, b :: y, 0 => rfl
  | a :: x, b :: y, i + 1 => by
    show (kAdd x y).getD i 0 = x.getD i 0 + y.getD i 0
    exact kAdd_getD x y i

theorem kMinL_getD : ∀ (x y : List Nat) (i : Nat),
    (kMinL x y).getD i 0 = min (x.getD i 0) (y.getD i 0)
  | [], l, i => by simp only [kMinL, getD_nil0, Nat.zero_min]
  | a :: x, [], i => by simp only [kMinL, getD_nil0, Nat.min_zero]
  | a :: x, b :: y, 0 => rfl
  | a :: x, b :: y, i + 1 => by
    show (kMinL x y).getD i 0 = min (x.getD i 0) (y.getD i 0)
    exact kMinL_getD x y i

theorem kShift_getD (row : List Nat) : ∀ (E S : Nat),
    (kShift E row).getD S 0 = if E ≤ S then row.getD (S - E) 0 else 0
  | 0, S => by simp [kShift]
  | E + 1, 0 => rfl
  | E + 1, S + 1 => by
    show (kShift E row).getD S 0 = _
    rw [kShift_getD row E S]
    by_cases h : E ≤ S
    · rw [if_pos h, if_pos (by omega)]; congr 1; omega
    · rw [if_neg h, if_neg (by omega)]

theorem getElem_eq_getD0 (l : List Nat) (i : Nat) (h : i < l.length) : l[i] = l.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem kPad_length : ∀ (n : Nat) (l : List Nat), (kPad n l).length = n
  | 0, _ => rfl
  | n + 1, [] => by simp [kPad, kPad_length n []]
  | n + 1, _ :: l => by simp [kPad, kPad_length n l]

theorem kPad_getD : ∀ (n : Nat) (l : List Nat) (i : Nat), i < n → (kPad n l).getD i 0 = l.getD i 0
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, [], 0, _ => rfl
  | n + 1, [], i + 1, h => by
    show (kPad n []).getD i 0 = _
    rw [kPad_getD n [] i (by omega)]; rfl
  | n + 1, _ :: l, 0, _ => rfl
  | n + 1, _ :: l, i + 1, h => by
    show (kPad n l).getD i 0 = l.getD i 0
    exact kPad_getD n l i (by omega)

/-- Zeile der rechten Seite: Summe der verschobenen Zeilen der Vorfahren-Klassen. -/
def kRowOf (J : Nat) (tab : List (List Nat)) (s : Nat) (Es : List Nat) : List Nat :=
  Es.foldr (fun E acc => kAdd (kShift E (tab.getD (cls J s E) [])) acc) []

def kRow (J Emax : Nat) (tab : List (List Nat)) (s : Nat) : List Nat :=
  kRowOf J tab s ((List.range' 1 Emax).filter (valid J s))

theorem kRowOf_getD (J : Nat) (tab : List (List Nat)) (s S : Nat) : ∀ Es : List Nat,
    (kRowOf J tab s Es).getD S 0 =
      (Es.map fun E => if E ≤ S then getT tab (cls J s E) (S - E) else 0).sum
  | [] => getD_nil0 S
  | E :: Es => by
    show (kAdd (kShift E (tab.getD (cls J s E) [])) (kRowOf J tab s Es)).getD S 0 = _
    rw [kAdd_getD, kShift_getD, kRowOf_getD J tab s S Es, List.map_cons, List.sum_cons]
    rfl

theorem range'_one_succ (n : Nat) : List.range' 1 (n + 1) = List.range' 1 n ++ [n + 1] := by
  rw [show n + 1 = n + 1 from rfl, ← List.range'_append (s := 1) (m := n) (n := 1)]
  simp [Nat.add_comm]

theorem sum_cut (p : Nat → Bool) (g : Nat → Nat) (S : Nat) : ∀ Emax : Nat,
    (((List.range' 1 Emax).filter p).map fun E => if E ≤ S then g E else 0).sum =
      (((List.range' 1 (min S Emax)).filter p).map g).sum
  | 0 => by simp
  | n + 1 => by
    rw [range'_one_succ, List.filter_append, List.map_append, List.sum_append_nat, sum_cut p g S n]
    by_cases h : n + 1 ≤ S
    · rw [show min S (n + 1) = n + 1 by omega, range'_one_succ, List.filter_append,
        List.map_append, List.sum_append_nat, show min S n = n by omega]
      congr 1
      by_cases hp : p (n + 1) = true
      · simp [hp, h]
      · simp [hp]
    · rw [show min S (n + 1) = min S n by omega]
      have : (([n + 1].filter p).map fun E => if E ≤ S then g E else 0).sum = 0 := by
        by_cases hp : p (n + 1) = true
        · simp [hp, show ¬ n + 1 ≤ S by omega]
        · simp [hp]
      rw [this, Nat.add_zero]

theorem kRow_getD (J Emax : Nat) (tab : List (List Nat)) (s S : Nat) :
    (kRow J Emax tab s).getD S 0 = rhsT J Emax tab s S := by
  unfold kRow rhsT Es
  rw [kRowOf_getD]
  exact sum_cut (valid J s) (fun E => getT tab (cls J s E) (S - E)) S Emax

/-- Schneller Tabellenschritt. -/
def fastNext (J Emax Smax : Nat) (tab : List (List Nat)) : List (List Nat) :=
  (List.range (3 ^ (J - 1))).map fun t =>
    kPad (Smax + 1) (kMinL (kRow J Emax tab t)
      (kMinL (kRow J Emax tab (t + 3 ^ (J - 1))) (kRow J Emax tab (t + 2 * 3 ^ (J - 1)))))

theorem fastNext_eq (J Emax Smax : Nat) (tab : List (List Nat)) :
    fastNext J Emax Smax tab = nextT J Emax Smax tab := by
  unfold fastNext nextT
  congr 1; funext t
  apply List.ext_getElem
  · simp [kPad_length]
  · intro i h1 h2
    have hi : i < Smax + 1 := by rw [kPad_length] at h1; exact h1
    rw [getElem_eq_getD0 _ _ h1, kPad_getD _ _ _ hi, kMinL_getD, kMinL_getD,
      kRow_getD, kRow_getD, kRow_getD, List.getElem_map, List.getElem_range]

def fastFrom (J Emax Smax : Nat) (L : List (List Nat)) : Nat → List (List Nat)
  | 0 => L
  | d + 1 => fastNext J Emax Smax (fastFrom J Emax Smax L d)

theorem fastFrom_eq (J Emax Smax : Nat) (L : List (List Nat)) :
    ∀ d, fastFrom J Emax Smax L d = tabFrom J Emax Smax L d
  | 0 => rfl
  | d + 1 => by
    show fastNext J Emax Smax (fastFrom J Emax Smax L d) = nextT J Emax Smax (tabFrom J Emax Smax L d)
    rw [fastNext_eq, fastFrom_eq J Emax Smax L d]

end Collatz

namespace Collatz

/-- Prüft `L₀ ≤ getT tab t S₀` für alle `t < n` mit `3 ∤ t`. -/
def allGe (L0 S0 n : Nat) (tab : List (List Nat)) : Bool :=
  (List.range n).all fun t => t % 3 == 0 || decide (L0 ≤ getT tab t S0)

theorem allGe_spec {L0 S0 n : Nat} {tab : List (List Nat)} (h : allGe L0 S0 n tab = true) :
    ∀ t, t < n → t % 3 ≠ 0 → L0 ≤ getT tab t S0 := by
  intro t ht h3
  unfold allGe at h
  rw [List.all_eq_true] at h
  have := h t (List.mem_range.mpr ht)
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this with h' | h'
  · exact absurd h' h3
  · exact h'

end Collatz

namespace Collatz

theorem tabFrom_tabQ (J Emax Smax d : Nat) :
    ∀ k, tabFrom J Emax Smax (tabQ J Emax Smax d) k = tabQ J Emax Smax (d + k)
  | 0 => rfl
  | k + 1 => by
    show nextT J Emax Smax (tabFrom J Emax Smax (tabQ J Emax Smax d) k) = tabQ J Emax Smax (d + k + 1)
    rw [tabFrom_tabQ J Emax Smax d k]; rfl

end Collatz
