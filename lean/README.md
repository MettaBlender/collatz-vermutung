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
| `Collatz/PowerDrop.lean` | Potenz-Abfall: fast alle n in [2^(32w), 2^(32w+1)) erreichen einen Wert x mit x^32 < 2·n^31; Ausnahmen-Anteil ≤ (3^32/2^51)^w → 0 (Korec-artig, für alle Grössenordnungen) |
| `Collatz/InverseTree.lean` | Rückwärtsbaum: jedes n mit 3 ∤ n hat beliebig grosse ungerade Vorfahren; unendlich viele ungerade Zahlen erreichen die 1 |
| `Collatz/TwoAdic.lean` | 2-adische Zahlen: die Paritätsfolge Q ist eine Bijektion Z₂ → {0,1}^ℕ und macht aus T die Verschiebung (Terras, Lagarias) |
| `Collatz/ParityCriterion.lean` | Collatz-Vermutung ⇔ die Paritätsfolge jeder Zahl endet in 1,0,1,0,… |
| `Collatz/OrbitDensity.lean` | Wachstumsschranke 2^k·M^o·T^k(n) ≤ (3M+1)^o·n; das kleinste Glied eines Gegenbeispiels hat für jedes k: 2^k·m^o ≤ (3m+1)^o (Lagarias) |
| `Collatz/OrbitDensity27.lean` | Mit m ≥ 2^27: mindestens 631 ungerade unter den ersten 1000 und 6310 unter den ersten 10 000 Schritten |
| `Collatz/Korec.lean` | Korec (Exponent 4/5): Σ p^o q^(k−o) = (p+q)^k (Chernoff); fast alle n erreichen x mit x^5 < 2·n^4, Ausnahmen ≤ 0.9685^w |
| `Collatz/Crandall.lean` | Crandall-Typ: binärer Baum ungerader Vorfahren ab 5; 2^t verschiedene Zahlen ≤ 5·22^t erreichen die 1 (für alle t), also ≥ ½·(x/5)^0.224 Zahlen ≤ x |
| `Collatz/Mixing.lean` | Lagarias (endliche Form): T ist masstreu und zwei-zu-eins; die ersten j Paritäten sind unabhängig von T^j(n) mod 2^k (genau ein r < 2^(j+k) pro Paar) |
| `Collatz/DenseTree.lean` | 2 ist Primitivwurzel modulo 3^J; jedes n mit 3 ∤ n hat Vorfahren in jeder Restklasse mod 2^k; gäbe es ein Gegenbeispiel, dann in jeder Restklasse mod 2^k |
| `Collatz/MinClasses.lean` | Das kleinste Glied eines Gegenbeispiels liegt mod 2^(1000w) in höchstens einem Anteil 2^(−49w) der Klassen (2-adische Nullmenge; Chernoff mit 630/370) |
| `Collatz/OddRuns.lean` | j ungerade Schritte am Stück ⇒ 2^j ∣ x+1; Mersenne T^j(2^j a − 1) = 3^j a − 1; keine Folge ist ab einem Punkt nur ungerade (anders als −1 in ℤ₂) |
| `Collatz/Steckbrief.lean` | Steckbrief: Gegenbeispiele in jeder Klasse mod 2^k, Minimum ≥ 2^27 in 2-adischer Nullmenge, und divergente Folge oder Zyklus der Länge 1719a + 38609b |
| `Collatz/ManyCounterexamples.lean` | Baum mit beliebiger Wurzel: gäbe es ein Gegenbeispiel r, dann 2^t verschiedene Gegenbeispiele ≤ r·22^t (für alle t) |
| `Collatz/DenseTree3.lean` | Vorfahren in jeder Klasse mod 2^k mit jedem Rest mod 3; gäbe es ein Gegenbeispiel, dann in jeder Klasse mod 3·2^k (auch durch 3 teilbare) |
| `Collatz/Records.lean` | Rekorde: jeder Rekord einer Folge ist 3x+1 mit x ungerade, also ≡ 4 mod 6; eine divergente Folge hat Rekorde über jeder Schranke |
| `Collatz/ThreeAdic.lean` | 3-adisch und 2-adisch zugleich: Vorfahren in jeder Klasse mod 2^k und mod 3^J; gäbe es ein Gegenbeispiel, dann in jeder Klasse mod 2^k·3^J; die Vermutung für eine solche Klasse genügt; dann sogar unendlich viele Gegenbeispiele in jeder Klasse (Satz 44) |
| `Collatz/Weighted.lean` | Gewichteter Crandall-Baum (Satz 45): das kleine Kind ist < 6n; C(t,a) verschiedene Zahlen ≤ 5·6^a·22^(t−a) erreichen die 1, Exponent ≈ 0.291 statt 0.224; ebenso für Gegenbeispiele |
| `Collatz/KrasikovClass.lean` | Satz 48: Satz 47 gilt in jeder Restklasse modulo 2^K, mit demselben Exponenten 0.665 und einer nur von K abhängigen Konstanten; ebenso für Gegenbeispiele |
| `Collatz/KrasikovClass6.lean` | Satz 49: dasselbe in jeder Restklasse modulo 2^K · 3^J (auch durch 3 teilbare Klassen), Exponent 0.665; ebenso für Gegenbeispiele |
| `Collatz/Ancestors.lean` | Satz 50: Vorfahren-Dichotomie: bei 3 ∣ n nur 2^j·n, bei 3 ∤ n mindestens 58525359050790615^k Vorfahren ≤ 6n·(2^163/3^50)^k, also etwa (x/n)^0.665 |
| `Collatz/ManyCounterexamples665.lean` | Satz 51: Gäbe es ein Gegenbeispiel, dann eines n (3 ∤ n) mit mindestens 58525359050790615^k Gegenbeispielen ≤ 6n·(2^163/3^50)^k, also etwa (x/6n)^0.665 (verbessert Satz 40 von 0.224) |
| `Collatz/CycleBasin.lean` | Satz 52: Jedes Zyklusglied n hat mindestens 58525359050790615^k Vorfahren ≤ 6n·(2^163/3^50)^k; bei einem nichttrivialen Zyklus sind das alles Gegenbeispiele |
| `Collatz/FourKids.lean` | Vier Kinder pro Knoten (Satz 46): mit c ist auch 64c+21 Vorfahre; C(t,a)·C(t,h) verschiedene Zahlen ≤ 5·6^a·22^(t−a)·64^h erreichen die 1, Exponent ≈ 0.374; ebenso für Gegenbeispiele |
| `Collatz/Krasikov.lean` | Rückwärtsbaum mit Buchführung modulo 3^J (Methode von Krasikov): allgemeiner Zählsatz aus einer Tabelle (Zertifikat) und Block-Iteration für alle Grössen |
| `Collatz/KrasikovFast.lean` | Zeilenweise Tabellenrechnung `fastNext` (verschieben, addieren, Minimum), bewiesen gleich `nextT`, für den Kernel etwa 25-mal schneller |
| `Collatz/KrasikovData5.lean`, `Collatz/KrasikovB5.lean` … `KrasikovB50.lean` | Zwischenstände der Tabelle (Klassen mod 243, E ≤ 14, S ≤ 163) und ihre Nachrechnung in zehn Etappen (je decide +kernel, ~30 s) |
| `Collatz/KrasikovBound.lean` | Satz 47: für jedes k gibt es 58525359050790615^k verschiedene Zahlen ≤ 5·(2^163/3^50)^k, die die 1 erreichen, also etwa x^0.665; ebenso für Gegenbeispiele |
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
| `Collatz/Verified25.lean` (+ `V25/G00`–`G63`) | Dasselbe von 2^24 bis 2^25 (128 Blöcke in 64 Dateien) |
| `Collatz/Verified25All.lean`, `CycleShape25.lean` | Alle `n < 2^25` erreichen die 1; ein weiterer Zyklus hat ≥ 14 271 ungerade Glieder, ≥ 36 890 Schritte, Länge 1719a + 35 171b |
| `Collatz/Verified26.lean` (+ `V26/H000`–`H255`) | Dasselbe von 2^25 bis 2^26 (256 Dateien mit je 256 Klassen) |
| `Collatz/Verified26All.lean`, `CycleShape26.lean` | Alle `n < 2^26` erreichen die 1; ein weiterer Zyklus hat ≥ 14 936 ungerade Glieder, ≥ 38 609 Schritte, Länge 1719a + 36 890b |
| `Collatz/Verified27.lean` (+ `V27/I000`–`I511`) | Dasselbe von 2^26 bis 2^27 (512 Dateien mit je 128 Klassen, in der CI in acht parallelen Jobs) |
| `Collatz/Verified27All.lean`, `CycleShape27.lean` | Alle `n < 2^27` erreichen die 1; ein weiterer Zyklus hat ≥ 15 601 ungerade Glieder, ≥ 40 328 Schritte, Länge 1719a + 38 609b |
| `Collatz/CycleShape.lean` | Form eines weiteren Zyklus über Stern-Brocot-Nachbarn: o = 665a + 11 611b ungerade Glieder, Länge 1719a + 30 014b mit a, b ≥ 1 |
| `Collatz/Binomial.lean` | Binomialverteilung der ungeraden Schritte: genau C(k, j) Klassen mod 2^k haben j ungerade unter den ersten k Schritten; Σ x^o = (1+x)^k |
| `Collatz/CoeffStopping.lean` | Koeffizienten-Stoppzeit τ ≤ Stoppzeit σ, Gleichheit für grosse n; Terras' Vermutung σ = τ (offen) würde alle weiteren T-Zyklen ausschliessen |
| `Collatz/ModThree.lean` | Vielfache von 3 kommen nur im Halbierungs-Anfangsstück vor; kein Zyklus enthält ein Vielfaches von 3 |
| `Collatz/Negative.lean` | Collatz auf ganzen Zahlen: drei Zyklen bei negativen Zahlen (-1, -5, -17), ein Beweis muss Positivität benutzen |
| `Collatz/CycleUnique.lean` | Böhm–Sontacchi: zu jedem Paritätsvektor gehört höchstens ein Zyklus, und auf Zyklen gilt 3^o < 2^p |
