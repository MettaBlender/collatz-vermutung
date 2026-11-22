"""Kopiert Bilder und Quelltexte aus dem Repo in den Ordner site/.

Vercel liefert site/ als statische Seite aus. Nach Änderungen an Skripten,
Beweisen oder Bildern einmal ausführen:

    python site/build.py
"""

import shutil
from pathlib import Path

root = Path(__file__).resolve().parent.parent
site = root / "site"

for sub in ("bilder", "quellen"):
    shutil.rmtree(site / sub, ignore_errors=True)

shutil.copytree(root / "docs" / "bilder", site / "bilder")
(site / "quellen" / "lean").mkdir(parents=True)
(site / "quellen" / "python").mkdir(parents=True)
for f in (root / "lean" / "Collatz").glob("*.lean"):
    shutil.copy(f, site / "quellen" / "lean" / f.name)
shutil.copy(root / "lean" / "AxiomCheck.lean", site / "quellen" / "lean" / "AxiomCheck.lean")
for f in (root / "python").glob("*.py"):
    if not f.name.startswith("test_"):
        shutil.copy(f, site / "quellen" / "python" / f.name)
print("site/ aktualisiert")
