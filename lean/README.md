# Lean-4-Formalisierung

Reines Lean 4 (v4.24.0, ohne Mathlib). Bauen mit `lake build`, Axiome prüfen mit
`lake env lean AxiomCheck.lean`.

**Wichtig:** Die Collatz-Vermutung selbst ist **nicht** bewiesen (sie ist ein offenes
Problem). `CollatzConjecture` ist nur als Aussage definiert. Alle Sätze unten sind
vollständig bewiesen, ohne `sorry` und ohne zusätzliche Axiome.

| Datei | Inhalt |
|---|---|
| `Collatz/Basic.lean` | `step`, `iter`, `ReachesOne`, `CollatzConjecture`; Zweierpotenzen erreichen 1; `2n` erreicht 1 ⇔ `n` erreicht 1 |
| `Collatz/Reduction.lean` | Reduktion auf Abstieg (endliche Stoppzeit); Abstieg für gerade Zahlen, `4a+1`, `16a+3`; Reduktion auf `n ≡ 7, 11, 15 (mod 16)`; `4n+1` und `n` (ungerade) laufen zusammen |
| `Collatz/Sieve.lean` | Verifiziertes Restklassen-Sieb mit Korrektheitsbeweis; nachgerechnet: mod 256 bleiben 19 Klassen, mod 4096 bleiben 226 |
| `Collatz/Sieve16.lean` | Sieb mod 2^16: nur 2114 von 65 536 Klassen (3.2 %) bleiben offen |
| `Collatz/Sieve20.lean` (+ `Sieve20A`–`D`, `Sieve20Count`) | Sieb mod 2^20 durch Hochheben der offenen Klassen mod 2^16: höchstens 27 328 von 1 048 576 Klassen (2.6 %) bleiben offen |
| `Collatz/Verified.lean` | Alle Zahlen 1 bis 10 000 erreichen die 1 (vom Kernel nachgerechnet, mit Korrektheitsbeweis des Prüfers) |
| `Collatz/VerifiedLarge.lean` | Alle Zahlen 1 bis 100 000 erreichen die 1 (nur `n ≡ 3 mod 4` geprüft, in Blöcken) |
| `Collatz/Cycles.lean` | Zyklen und Gegenbeispiele: jeder Zyklus, der die 1 erreicht, ist `1 → 4 → 2`; ein Gegenbeispiel enthält nur Zahlen > 100 000, und sein kleinstes Folgenglied liegt in einer der 2114 offenen Restklassen mod 2^16 |
| `Collatz/Tree.lean` | Collatz-Baum: Vorgänger-Charakterisierung; Vielfache von 3 haben nur den Vorgänger `2n`; ungerade Vorgänger genau für `n ≡ 4 (mod 6)`; jede Folge zur 1 läuft über die 16 |
| `Collatz/Climb.lean` | Beliebig lange Anstiege: `2^k·a − 1` wird nach `2k` Schritten zu `3^k·a − 1` und fällt unterwegs nie unter den Start; es gibt keine feste Abstiegszeit |
| `Collatz/Terras.lean` | Satz von Terras: Der Paritätsvektor der Länge k hängt nur von n mod 2^k ab, und jeder Vektor gehört zu genau einer Klasse; affine Formel T^k(r + 2^k·a) = T^k(r) + 3^o·a; Abstiegskriterium 3^o < 2^k; Zyklusgleichung n·(2^p − 3^o) = c |
| `Collatz/Density.lean` | Fast alle Zahlen fallen ab: Σ 2^o = 3^k über die Klassen mod 2^k; bei 2·3^o ≤ 2^k fällt jedes n ≥ 2^k der Klasse ab; der Anteil der Ausnahmen geht gegen 0 (Terras/Everett) |
| `Collatz/OneCycle.lean` | 1-Zyklen (Steiner-Typ): Gleichung n·(2^(o+e) − 3^o) = 3^o − 2^o; kein nichttrivialer 1-Zyklus mit o ≤ 30 000 ungeraden Schritten |
| `Collatz/Counterexample.lean` | Steckbrief eines Gegenbeispiels (kleinstes Glied ≥ 2^22, offene Klasse mod 2^20, mindestens 14 ungerade unter den ersten 22 Schritten); Vermutung für `T` ⇔ Vermutung für die Collatz-Abbildung |
| `Collatz/Variants.lean` | Varianten qn+1: unter 5n+1 erreicht die 13 nie die 1 (Zyklus), unter n+1 erreicht jede Zahl die 1 |
| `Collatz/Dichotomy.lean` | Vermutung ⇔ alle Folgen beschränkt und kein nichttrivialer Zyklus (mit Schubfachprinzip) |
| `Collatz/CycleLength.lean` | Jeder nichttriviale Zyklus hat mindestens 971 ungerade Glieder und 2510 Schritte |
| `Collatz/CycleCheck.lean` | Schnelle Kernel-Prüfung der Zyklus-Ungleichung (Potenzen laufen mit) und allgemeine Schranke `cycle_odd_gt` |
| `Collatz/VerifiedHuge.lean` (+ `VerifiedHugeA`–`H`) | Nachrechnen nur in den offenen Klassen mod 2^16: alle Zahlen unter 2^22 fallen ab (64 Blöcke) |
| `Collatz/VerifiedHugeAll.lean` | Alle `n < 2^22` erreichen die 1; ein weiterer Zyklus enthält nur Zahlen ≥ 2^22 und hat ≥ 7621 ungerade Glieder und ≥ 19 700 Schritte; das kleinste Glied eines Gegenbeispiels liegt in einer offenen Klasse mod 2^20 |
| `Collatz/Verified24.lean` (+ `V24/F00`–`F31`) | Nachrechnen nur in den 27 328 offenen Klassen mod 2^20: alle Zahlen von 2^22 bis 2^24 fallen ab (128 Blöcke) |
| `Collatz/Verified24All.lean` | Alle `n < 2^24` erreichen die 1; ein weiterer Zyklus enthält nur Zahlen ≥ 2^24 und hat ≥ 12 276 ungerade Glieder und ≥ 31 733 Schritte |
| `Collatz/CycleShape.lean` | Form eines weiteren Zyklus über Stern-Brocot-Nachbarn: o = 665a + 11 611b ungerade Glieder, Länge 1719a + 30 014b mit a, b ≥ 1 |
| `Collatz/Binomial.lean` | Binomialverteilung der ungeraden Schritte: genau C(k, j) Klassen mod 2^k haben j ungerade unter den ersten k Schritten; Σ x^o = (1+x)^k |
| `Collatz/CoeffStopping.lean` | Koeffizienten-Stoppzeit τ ≤ Stoppzeit σ, Gleichheit für grosse n; Terras' Vermutung σ = τ (offen) würde alle weiteren T-Zyklen ausschliessen |
| `Collatz/ModThree.lean` | Vielfache von 3 kommen nur im Halbierungs-Anfangsstück vor; kein Zyklus enthält ein Vielfaches von 3 |
| `Collatz/Negative.lean` | Collatz auf ganzen Zahlen: drei Zyklen bei negativen Zahlen (-1, -5, -17), ein Beweis muss Positivität benutzen |
| `Collatz/CycleUnique.lean` | Böhm–Sontacchi: zu jedem Paritätsvektor gehört höchstens ein Zyklus, und auf Zyklen gilt 3^o < 2^p |
