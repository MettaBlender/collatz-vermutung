// --- KaTeX ---
window.addEventListener("load", () => {
  if (window.renderMathInElement) {
    renderMathInElement(document.body, {
      delimiters: [{ left: "$$", right: "$$", display: true }, { left: "$", right: "$", display: false }],
    });
  }
});

// --- Folge berechnen (mit BigInt, damit auch grosse Zahlen gehen) ---
function folge(n) {
  const f = [n];
  while (n !== 1n) { n = n % 2n === 0n ? n / 2n : 3n * n + 1n; f.push(n); if (f.length > 100000) break; }
  return f;
}
function zeichne(f) {
  const c = document.getElementById("folge-plot");
  const dpr = window.devicePixelRatio || 1;
  const w = c.clientWidth, h = 260;
  c.width = w * dpr; c.height = h * dpr;
  const g = c.getContext("2d"); g.scale(dpr, dpr);
  const css = getComputedStyle(document.documentElement);
  const ys = f.map(v => Math.log10(Number(v)));
  const maxY = Math.max(...ys, 1), pad = 36;
  g.clearRect(0, 0, w, h);
  g.strokeStyle = css.getPropertyValue("--line"); g.fillStyle = css.getPropertyValue("--muted");
  g.font = "12px system-ui"; g.lineWidth = 1;
  for (let p = 0; p <= Math.ceil(maxY); p++) {
    const y = h - pad / 2 - (p / Math.ceil(maxY)) * (h - pad);
    g.beginPath(); g.moveTo(pad, y); g.lineTo(w - 8, y); g.stroke();
    g.fillText("10^" + p, 2, y + 4);
  }
  g.strokeStyle = css.getPropertyValue("--accent"); g.lineWidth = 1.5; g.beginPath();
  ys.forEach((y, i) => {
    const x = pad + (i / Math.max(1, ys.length - 1)) * (w - pad - 8);
    const yy = h - pad / 2 - (y / Math.ceil(maxY)) * (h - pad);
    i ? g.lineTo(x, yy) : g.moveTo(x, yy);
  });
  g.stroke();
}
function berechne() {
  let n;
  try { n = BigInt(document.getElementById("startzahl").value); } catch { return; }
  if (n < 1n) return;
  const f = folge(n);
  const max = f.reduce((a, b) => (b > a ? b : a), 0n);
  document.getElementById("folge-info").textContent =
    `${n} erreicht die 1 nach ${f.length - 1} Schritten. Grösster Wert: ${max}.`;
  document.getElementById("folge-werte").textContent = f.join(" → ");
  zeichne(f);
}
document.getElementById("los").addEventListener("click", berechne);
document.getElementById("startzahl").addEventListener("keydown", e => { if (e.key === "Enter") berechne(); });
window.addEventListener("resize", berechne);
berechne();

// --- Quelltexte anzeigen ---
async function tabs(containerId, codeId, files, base) {
  const box = document.getElementById(containerId), pre = document.getElementById(codeId);
  const show = async (f, btn) => {
    [...box.children].forEach(b => b.classList.remove("on")); btn.classList.add("on");
    pre.textContent = await (await fetch(base + f)).text();
  };
  files.forEach((f, i) => {
    const b = document.createElement("button"); b.textContent = f;
    b.onclick = () => show(f, b); box.appendChild(b);
    if (i === 0) show(f, b);
  });
}
tabs("lean-tabs", "lean-code",
  ["Basic.lean", "Reduction.lean", "Sieve.lean", "Sieve16.lean", "Verified.lean", "VerifiedLarge.lean", "Cycles.lean", "Tree.lean", "AxiomCheck.lean"], "quellen/lean/");
tabs("py-tabs", "py-code",
  ["collatz_core.py", "collatz_verteilung.py", "stoppzeiten.py", "sieb.py", "trajektorien.py", "zyklen.py", "verifizieren.py", "baum.py", "paritaet.py"], "quellen/python/");

// --- Python im Browser (Pyodide) ---
const BEISPIELE = {
  "Folge von 27": `from collatz_core import folge, gesamtstoppzeit, maximum

n = 27
print(folge(n))
print("Schritte:", gesamtstoppzeit(n), " Maximum:", maximum(n))`,
  "Verifizieren bis N": `# Es genügt zu prüfen, dass jede Zahl n > 1 unter n fällt (Lean: conjecture_of_descends).
# Gerade Zahlen und n ≡ 1 (mod 4) fallen bewiesenermassen, also nur n ≡ 3 (mod 4) prüfen.
N = 200_000
laengste = (0, 0)
for n in range(3, N + 1, 4):
    x, k = n, 0
    while x >= n:
        x = x // 2 if x % 2 == 0 else 3 * x + 1
        k += 1
    laengste = max(laengste, (k, n))
print(f"Alle Zahlen bis {N} erreichen die 1.")
print("Längste Stoppzeit:", laengste[0], "Schritte bei n =", laengste[1])`,
  "Restklassen-Sieb": `from collatz_core import sieb_ueberlebende_bis

stufen = sieb_ueberlebende_bis(18)
for k, s in enumerate(stufen):
    print(f"mod 2^{k:<2} = {2**k:>7}: {len(s):>6} offen  ({len(s)/2**k:7.3%})")
print("offen mod 16:", sorted(stufen[4]))`,
  "Rekorde": `from collatz_core import gesamtstoppzeiten

t = gesamtstoppzeiten(100_000)
best = -1
for n in range(1, len(t)):
    if t[n] > best:
        best = t[n]
        print(f"{n:>7}: {best} Schritte")`,
  "Negative Zyklen": `def schritt(n):
    return n // 2 if n % 2 == 0 else 3 * n + 1

gefunden = set()
for start in range(-500, 0):
    gesehen, x = set(), start
    while x not in gesehen:
        gesehen.add(x)
        x = schritt(x)
    z, y = [x], schritt(x)
    while y != x:
        z.append(y); y = schritt(y)
    gefunden.add(tuple(sorted(z)))
for z in sorted(gefunden, key=len):
    print(len(z), "Glieder:", sorted(z, key=abs)[:6], "…" if len(z) > 6 else "")`,
};
const code = document.getElementById("code");
const ex = document.getElementById("beispiele");
Object.keys(BEISPIELE).forEach((k, i) => {
  const b = document.createElement("button"); b.textContent = k;
  b.onclick = () => { [...ex.children].forEach(x => x.classList.remove("on")); b.classList.add("on"); code.value = BEISPIELE[k]; };
  ex.appendChild(b); if (i === 0) b.click();
});

let pyodide = null;
const runBtn = document.getElementById("ausfuehren");
const out = document.getElementById("ausgabe");
async function ladePython() {
  const s = document.createElement("script");
  s.src = "https://cdn.jsdelivr.net/pyodide/v0.26.4/full/pyodide.js";
  s.onload = async () => {
    pyodide = await loadPyodide();
    const core = await (await fetch("quellen/python/collatz_core.py")).text();
    pyodide.FS.writeFile("collatz_core.py", core);
    runBtn.disabled = false; runBtn.textContent = "Ausführen";
  };
  document.head.appendChild(s);
}
runBtn.addEventListener("click", async () => {
  runBtn.disabled = true; runBtn.textContent = "Läuft …"; out.textContent = "";
  let buf = "";
  pyodide.setStdout({ batched: t => { buf += t + "\n"; } });
  pyodide.setStderr({ batched: t => { buf += t + "\n"; } });
  const t0 = performance.now();
  try { await pyodide.runPythonAsync(code.value); }
  catch (e) { buf += String(e); }
  out.textContent = buf + `\n(${((performance.now() - t0) / 1000).toFixed(2)} s)`;
  runBtn.disabled = false; runBtn.textContent = "Ausführen";
});
// Python erst laden, wenn der Abschnitt in Sicht kommt
new IntersectionObserver((e, o) => { if (e[0].isIntersecting) { ladePython(); o.disconnect(); } })
  .observe(document.getElementById("python"));
