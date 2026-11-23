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
  ["Basic.lean", "Reduction.lean", "Sieve.lean", "Sieve16.lean", "Sieve20.lean", "Sieve20Count.lean", "Verified.lean", "VerifiedLarge.lean", "Cycles.lean", "Tree.lean", "Climb.lean", "Variants.lean", "Dichotomy.lean", "CycleLength.lean", "CycleCheck.lean", "VerifiedHuge.lean", "VerifiedHugeAll.lean", "Verified24.lean", "Verified24All.lean", "Verified25.lean", "Verified25All.lean", "Verified26.lean", "Verified26All.lean", "Verified27.lean", "Verified27All.lean", "Terras.lean", "Density.lean", "OneCycle.lean", "Counterexample.lean", "CycleShape.lean", "CycleShape25.lean", "CycleShape26.lean", "CycleShape27.lean", "Binomial.lean", "CoeffStopping.lean", "ModThree.lean", "Negative.lean", "CycleUnique.lean", "PowerDrop.lean", "InverseTree.lean", "TwoAdic.lean", "ParityCriterion.lean", "OrbitDensity.lean", "OrbitDensity27.lean", "Korec.lean", "Crandall.lean", "Mixing.lean", "DenseTree.lean", "MinClasses.lean", "OddRuns.lean", "Steckbrief.lean", "ManyCounterexamples.lean", "DenseTree3.lean", "Records.lean", "ThreeAdic.lean", "Weighted.lean", "FourKids.lean", "Krasikov.lean", "KrasikovFast.lean", "KrasikovBound.lean", "KrasikovClass.lean", "AxiomCheck.lean"], "quellen/lean/");
tabs("py-tabs", "py-code",
  ["collatz_core.py", "collatz_verteilung.py", "stoppzeiten.py", "sieb.py", "trajektorien.py", "zyklen.py", "verifizieren.py", "baum.py", "paritaet.py", "varianten.py", "zyklen_laenge.py", "zyklus_gleichung.py", "einszyklen.py", "koeffizienten_stoppzeit.py", "vielfache_drei.py", "paritaetszyklen.py", "potenz_abfall.py", "zweiadisch.py", "ungerade_dichte.py", "crandall.py", "masstreue.py", "vorfahren_klassen.py", "ungerade_laeufe.py"], "quellen/python/");

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

// --- Sieb-Explorer (gleicher Algorithmus wie Collatz.check in Lean) ---
function siebWeg(k, r) {
  const N = 1n << BigInt(k);
  let M = N, s = r;
  const weg = [`${M}a+${s}`];
  for (let i = 0; i < 400; i++) {
    if (M < N && (s < r || (s <= r && r <= 1n))) return { ok: true, weg };
    if (M % 2n === 1n) return { ok: false, weg };
    if (s % 2n === 0n) { M /= 2n; s /= 2n; } else { M *= 3n; s = 3n * s + 1n; }
    weg.push(`${M}a+${s}`);
  }
  return { ok: false, weg };
}
function siebPruefen() {
  const k = Math.max(1, Math.min(40, parseInt(document.getElementById("sieb-k").value) || 1));
  let r;
  try { r = BigInt(document.getElementById("sieb-r").value); } catch { return; }
  const N = 1n << BigInt(k);
  r = ((r % N) + N) % N;
  const { ok, weg } = siebWeg(k, r);
  document.getElementById("sieb-info").textContent = ok
    ? `Alle Zahlen ${N}a+${r} (ausser 1) fallen nach ${weg.length - 1} Schritten unter ihren Startwert.`
    : `Die Restklasse ${r} mod ${N} bleibt offen: der Koeffizient vor a wird ungerade, bevor die Folge sicher fällt. Grösseres k hilft vielleicht.`;
  document.getElementById("sieb-weg").textContent = weg.join(" → ");
}
function siebZaehlen() {
  let offen = [0n];  // mod 2^0
  const zeilen = [];
  for (let k = 1; k <= 22; k++) {
    const N = 1n << BigInt(k), H = N >> 1n, neu = [];
    for (const r of offen) for (const t of [r, r + H]) if (!siebWeg(k, t).ok) neu.push(t);
    offen = neu;
    zeilen.push(`k=${k}: ${offen.length} offen (${(100 * offen.length / Number(N)).toFixed(2)} %)`);
  }
  document.getElementById("sieb-info").textContent = "Offene Restklassen modulo 2^k:";
  document.getElementById("sieb-weg").textContent = zeilen.join(" · ");
}
document.getElementById("sieb-los").addEventListener("click", siebPruefen);
document.getElementById("sieb-zaehlen").addEventListener("click", siebZaehlen);
siebPruefen();

// ---------- Satz von Terras: Paritätsvektor -> Restklasse ----------
function T(n) { return n % 2n === 0n ? n / 2n : (3n * n + 1n) / 2n; }
function paritaeten(n, k) {
  const v = [];
  for (let i = 0; i < k; i++) { v.push(n % 2n === 1n ? "1" : "0"); n = T(n); }
  return v.join("");
}
function restklasseVon(bits) {
  // wie in Lean (parVec_surjective): von hinten aufbauen, 3 wird modulo 2^i invertiert
  let r = 0n;
  for (let i = 0; i < bits.length; i++) {
    const b = bits[bits.length - 1 - i], K = 1n << BigInt(i);
    if (b === "1") {
      const inv = K % 3n === 1n ? (2n * K + 1n) / 3n : (K + 1n) / 3n;
      const x = K === 1n ? 0n : (((inv * (r - 2n)) % K) + K) % K;
      r = 2n * x + 1n;
    } else r = 2n * r;
  }
  return r;
}
function terrasZeigen() {
  const bits = (document.getElementById("terras-v").value.match(/[01]/g) || []).join("").slice(0, 200);
  if (!bits) return;
  const k = bits.length, N = 1n << BigInt(k), r = restklasseVon(bits);
  const zeilen = [0n, 1n, 2n].map(a => `${r + a * N}: ${paritaeten(r + a * N, k)}`);
  document.getElementById("terras-info").textContent =
    `Paritätsvektor ${bits} (Länge ${k}) gehört genau zur Restklasse ${r} modulo 2^${k} = ${N}.`;
  document.getElementById("terras-weg").textContent = "Probe: " + zeilen.join(" · ");
}
if (document.getElementById("terras-los")) {
  document.getElementById("terras-los").addEventListener("click", terrasZeigen);
  terrasZeigen();
}

// ---------- Übersicht der Sätze (aus den Überschriften erzeugt) ----------
(function () {
  const liste = document.getElementById("satz-liste");
  if (!liste) return;
  for (const h of document.querySelectorAll("#beweise .theorem h4")) {
    const m = h.textContent.match(/^Satz (\d+): /);
    if (!m) continue;
    const id = "satz-" + m[1];
    h.parentElement.id = id;
    const li = document.createElement("li");
    li.value = Number(m[1]);
    const a = document.createElement("a");
    a.href = "#" + id;
    a.innerHTML = h.innerHTML.replace(/^Satz \d+: /, "");
    li.appendChild(a);
    liste.appendChild(li);
  }
})();
