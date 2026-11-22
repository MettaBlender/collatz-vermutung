# Collatz-Vermutung

Erforschung der Collatz-Vermutung mit Python (und später Lean).

**Die Vermutung:** Startet man mit einer beliebigen positiven ganzen Zahl und wendet immer wieder

- `n` gerade → `n / 2`
- `n` ungerade → `3n + 1`

an, so landet man irgendwann bei 1. Das ist bis heute **unbewiesen** (ein offenes Problem der Mathematik).
Per Computer wurde es für alle Startzahlen bis über 2^68 geprüft.

## Skript: Wie oft wird jede Zahl besucht?

`python/collatz_verteilung.py` rechnet die Folgen aller Startzahlen 1 bis N durch und zählt,
in wie vielen Folgen jede Zahl vorkommt. Danach zeigt es drei Diagramme:

1. Besuche pro Zahl für die kleinen Zahlen (blau = gerade, orange = ungerade)
2. Die meistbesuchten Zahlen
3. Wie viele Zahlen genau k-mal besucht werden (log-log)

```bash
cd python
pip install -r requirements.txt
python collatz_verteilung.py 100000                 # öffnet ein Fenster
python collatz_verteilung.py 100000 --bis 500 --top 25
python collatz_verteilung.py 100000 --ausgabe bild.png
python -m pytest                                    # Tests
```

Das Zählen nutzt aus, dass alle Folgen zusammen einen Baum mit der Wurzel 1 bilden. So wird jede Zahl
nur einmal berechnet. 100'000 Startzahlen dauern nur wenige Sekunden.

![Verteilung für Startzahlen bis 100'000](docs/bilder/verteilung.png)

**Was man sieht:**

- Jede Folge, die nicht schon bei 1, 2, 4 oder 8 startet, läuft über 16 → 8 → 4 → 2 → 1. Die Zahl 8 hat
  nämlich nur einen Vorgänger (16), weil `3n + 1 = 8` keine ganzzahlige Lösung hat. Die 16 selbst wird
  meistens über 5 erreicht (5 → 16), deshalb steht 5 gleich dahinter.
- Die sehr niedrigen Balken im oberen Diagramm gehören zu Vielfachen von 3. Eine solche Zahl kann nie
  aus `3n + 1` entstehen, sie wird also nur von ihren Verdopplungen (m, 2m, 4m, ...) erreicht.
- Die Besuchszahlen folgen ungefähr einem Potenzgesetz: viele Zahlen werden genau einmal besucht,
  ganz wenige sehr oft.
