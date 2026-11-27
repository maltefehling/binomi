/* Terme-Check – gemeinsame Aufgaben-Logik für Schülerseite (index.html) und Lehrerseite (lehrer.html).
   Aufbau wie der Wurzel-Check (Kl. 9). Alle Aufgaben sind eigene Zufallsgeneratoren; statt Math.random() benutzen sie rand(),
   damit ein Test aus Testcode + Listennummer exakt reproduzierbar ist. */
"use strict";
const $ = id => document.getElementById(id);
let rand = Math.random;
/* Test = Grundlagen (★ bis ★★, Malte 27.11.2026): schwerere Varianten nur in der Übung */
let IM_TEST = false;

/* ---------- Reproduzierbarer Zufall ---------- */
function mulberry32(a) {
  return function () {
    a |= 0; a = a + 0x6D2B79F5 | 0;
    let t = Math.imul(a ^ a >>> 15, 1 | a);
    t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
    return ((t ^ t >>> 14) >>> 0) / 4294967296;
  };
}
function hash32(str) {
  let h1 = 0xdeadbeef, h2 = 0x41c6ce57;
  for (let i = 0; i < str.length; i++) {
    const c = str.charCodeAt(i);
    h1 = Math.imul(h1 ^ c, 2654435761); h2 = Math.imul(h2 ^ c, 1597334677);
  }
  h1 = Math.imul(h1 ^ (h1 >>> 16), 2246822507) ^ Math.imul(h2 ^ (h2 >>> 13), 3266489909);
  h2 = Math.imul(h2 ^ (h2 >>> 16), 2246822507) ^ Math.imul(h1 ^ (h1 >>> 13), 3266489909);
  return (h1 ^ h2) >>> 0;
}

/* ---------- Hilfsfunktionen ---------- */
const R = (a, b) => a + Math.floor(rand() * (b - a + 1));
const pick = arr => arr[Math.floor(rand() * arr.length)];
const shuffle = arr => { for (let i = arr.length - 1; i > 0; i--) { const j = Math.floor(rand() * (i + 1)); [arr[i], arr[j]] = [arr[j], arr[i]]; } return arr; };
const eq = (a, b) => Math.abs(a - b) <= 1e-9 * Math.max(1, Math.abs(b));

function fmt(x) {
  x = Number(x.toPrecision(12));
  const neg = x < 0; x = Math.abs(x);
  let s = x.toFixed(10).replace(/0+$/, '').replace(/\.$/, '');
  let [i, d] = s.split('.');
  if (i.length > 4) i = i.replace(/\B(?=(\d{3})+(?!\d))/g, ' ');
  return (neg ? '−' : '') + i + (d ? ',' + d : '');
}
/* Nachsichtig bei „=“ (Schülerfeedback 4.11.2026: Rechenweg „4 · 5y + 4 · (−5) = 20y − 20“ oder „x = 12“ wurde nicht gelesen):
   gewertet wird, was nach dem letzten „=“ steht (steht danach nichts, das Stück davor). */
function nachGleich(s) { const p = String(s).split('='); for (let i = p.length - 1; i >= 0; i--) if (p[i].trim()) return p[i]; return ''; }
function parseNum(s) {
  s = nachGleich(s).trim().replace(/[\s  ']/g, '').replace(/^[−–]/, '-').replace(/^\+/, '');
  if (!s) return NaN;
  if (s.includes(',')) s = s.replace(/\./g, '').replace(',', '.');
  else if (/^-?\d{1,3}(\.\d{3})+$/.test(s)) s = s.replace(/\./g, '');
  return /^-?\d*\.?\d+$/.test(s) ? Number(s) : NaN;
}
const frac = (z, n) => `<span class="fr"><span>${z}</span><span>${n}</span></span>`;
const ggT = (a, b) => b ? ggT(b, a % b) : Math.abs(a);

/* ================= Terme lesen und prüfen =================
   Eingabe als Text (z. B. „6x² − 15x“, „6x^2-15x“, „6x2-15x“, „3(2x+5)“, „(x+4)²“).
   Gerechnet wird mit Polynomen (Koeffizienten je Glied), damit gleichwertige Terme sicher erkannt werden.
   Danach wird die FORM geprüft: ausmultipliziert und zusammengefasst ('sum'),
   möglichst großer Faktor ausgeklammert ('factor') oder als binomische Klammer geschrieben ('binom'). */
function termNorm(src) {
  return nachGleich(src).replace(/<sup>(\d+)<\/sup>/g, '^$1').replace(/\s+/g, '').replace(/[−–—]/g, '-').replace(/[·×∙•*]/g, '*')
    .replace(/,/g, '.').replace(/²/g, '^2').replace(/³/g, '^3').toLowerCase()
    .replace(/([a-z])(\d+)/g, '$1^$2')                 // iPads haben keine Hochzahl-Taste: x2 heißt x²
    .replace(/\)([23])(?![\d.^])/g, ')^$1');          // (x+3)2 heißt (x+3)²
}
function termParse(src) {
  const s = termNorm(src);
  if (!s) return { empty: true };
  const toks = s.match(/\d+(?:\.\d+)?|[a-z]|[-+*^()]/g) || [];
  if (toks.join('') !== s) return { error: true };
  let i = 0;
  const peek = () => toks[i], next = () => toks[i++];
  const isAtomStart = t => t !== undefined && (/^[\d.a-z]/.test(t) || t === '(');
  function sum() {
    const parts = [];
    let neg = false;
    if (peek() === '+' || peek() === '-') neg = next() === '-';
    parts.push({ neg, n: prod() });
    while (peek() === '+' || peek() === '-') { const n = next() === '-'; parts.push({ neg: n, n: prod() }); }
    return parts.length === 1 && !parts[0].neg ? parts[0].n : { t: 'sum', parts };
  }
  function prod() {
    const f = [factor()];
    while (peek() === '*' || isAtomStart(peek())) { if (peek() === '*') next(); f.push(factor()); }
    return f.length === 1 ? f[0] : { t: 'prod', f };
  }
  function factor() {
    if (peek() === '-') { next(); return { t: 'neg', x: factor() }; }
    const b = atom();
    if (peek() === '^') { next(); const e = next(); if (!/^\d$/.test(e || '')) throw 0; return { t: 'pow', b, e: +e }; }
    return b;
  }
  function atom() {
    const t = next();
    if (t === undefined) throw 0;
    if (/^[\d.]/.test(t)) return { t: 'num', v: Number(t) };
    if (/^[a-z]$/.test(t)) return { t: 'var', n: t };
    if (t === '(') { const e = sum(); if (next() !== ')') throw 0; return { t: 'par', x: e }; }
    throw 0;
  }
  try {
    const ast = sum();
    if (i !== toks.length) return { error: true };
    return { ast, hasParen: toks.includes('('), poly: toPoly(ast) };
  } catch (e) { return { error: true }; }
}
/* Polynom = { Schlüssel: Koeffizient }, Schlüssel z. B. "a1b2" (Variablen sortiert), "" = Zahl ohne Variable */
const keyObj = k => { const o = {}; (k.match(/[a-z]\d+/g) || []).forEach(m => o[m[0]] = +m.slice(1)); return o; };
const objKey = o => Object.keys(o).sort().filter(v => o[v]).map(v => v + o[v]).join('');
const pClean = p => { Object.keys(p).forEach(k => { if (Math.abs(p[k]) < 1e-9) delete p[k]; }); return p; };
function pAdd(p, q, s = 1) { const r = { ...p }; for (const k in q) r[k] = (r[k] || 0) + s * q[k]; return pClean(r); }
function pMul(p, q) {
  const r = {};
  for (const a in p) for (const b in q) {
    const o = keyObj(a), o2 = keyObj(b); for (const v in o2) o[v] = (o[v] || 0) + o2[v];
    const k = objKey(o); r[k] = (r[k] || 0) + p[a] * q[b];
  }
  return pClean(r);
}
function toPoly(n) {
  switch (n.t) {
    case 'num': return pClean({ '': n.v });
    case 'var': return { [n.n + '1']: 1 };
    case 'par': return toPoly(n.x);
    case 'neg': return pAdd({}, toPoly(n.x), -1);
    case 'sum': return n.parts.reduce((p, x) => pAdd(p, toPoly(x.n), x.neg ? -1 : 1), {});
    case 'prod': return n.f.reduce((p, x) => pMul(p, toPoly(x)), { '': 1 });
    case 'pow': { let p = { '': 1 }; const b = toPoly(n.b); for (let k = 0; k < n.e; k++) p = pMul(p, b); return p; }
  }
}
const pEq = (p, q) => Object.keys(pAdd(p, q, -1)).length === 0;
const nTerms = p => Object.keys(p).length;
const kDeg = k => (k.match(/\d+/g) || []).reduce((s, d) => s + +d, 0);
/* Faktoren eines Produkts: (x+3)² zählt als zwei Faktoren (x+3); Minus davor wird ignoriert. null = kein Produkt */
function productFactors(ast) {
  let n = ast;
  while (n.t === 'neg' || (n.t === 'sum' && n.parts.length === 1)) n = n.t === 'neg' ? n.x : n.parts[0].n;
  const out = [];
  const add = x => {
    if (x.t === 'neg') return add(x.x);
    if (x.t === 'prod') return x.f.forEach(add);
    if (x.t === 'pow' && x.b.t === 'par') { for (let k = 0; k < x.e; k++) out.push(toPoly(x.b)); return; }
    out.push(toPoly(x));
  };
  if (n.t === 'prod' || (n.t === 'pow' && n.b.t === 'par')) { add(n); return out; }
  return null;
}
/* „Primitiv“: Koeffizienten ganzzahlig ohne gemeinsamen Teiler und keine Variable in allen Gliedern */
function primitive(p) {
  const ks = Object.keys(p), cs = ks.map(k => p[k]);
  if (!cs.every(c => Number.isInteger(c))) return false;
  if (cs.reduce((g, c) => ggT(g, c), 0) !== 1) return false;
  const vs = ks.map(keyObj);
  return !Object.keys(vs[0]).some(v => vs.every(o => o[v]));
}
function gradeTerm(t, src) {
  const r = termParse(src);
  if (r.empty) return -1;
  if (r.error) return 0;
  if (!pEq(r.poly, termParse(t.target).poly)) return 0;
  if (t.form === 'sum') {
    const parts = r.ast.t === 'sum' ? r.ast.parts.map(p => p.n) : [r.ast];
    return !r.hasParen && parts.length === nTerms(r.poly) && parts.every(fertigesGlied) ? 2 : 1;
  }
  const f = productFactors(r.ast);
  if (!f) return 0;                                           // nicht faktorisiert – die Aufgabe ist ja gerade das Faktorisieren
  const sums = f.filter(p => nTerms(p) >= 2);
  if (!sums.length) return 0;
  if (t.form === 'factor') return sums.every(primitive) ? 2 : 1;
  if (t.form === 'binomK') {   // erst ausklammern, dann binomisch: 3x² − 27 = 3 · (x + 3) · (x − 3)
    const ok = sums.every(p => primitive(p) && Object.keys(p).every(k => kDeg(k) <= 1)) && f.every(p => nTerms(p) >= 2 || Object.keys(p).every(k => k === ''));
    return ok ? 2 : 1;
  }
  if (t.form === 'binom') return sums.every(p => primitive(p) && Object.keys(p).every(k => kDeg(k) <= 1)) && f.every(p => nTerms(p) >= 2 || (nTerms(p) === 1 && Math.abs(p['']) === 1)) ? 2 : 1;
  return 0;
}
/* Ein fertiges Glied: höchstens eine Zahl, jede Variable nur einmal (3x² statt 3 · 4x oder x · x) */
function fertigesGlied(n) {
  const f = [];
  const add = x => x.t === 'neg' ? add(x.x) : x.t === 'prod' ? x.f.forEach(add) : f.push(x);
  add(n);
  const vars = f.map(x => x.t === 'var' ? x.n : x.t === 'pow' && x.b.t === 'var' ? x.b.n : null).filter(Boolean);
  return f.filter(x => x.t === 'num' || (x.t === 'pow' && x.b.t === 'num')).length <= 1 && new Set(vars).size === vars.length;
}
/* Eingabe lesbar anzeigen (Vorschau, Lehrerseite) */
const escH = s => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
function termHtml(src) {
  return escH(termNorm(src)).replace(/\^(\d)/g, '<sup>$1</sup>').replace(/\*/g, ' · ').replace(/\./g, ',')
    .replace(/([^(])([+-])/g, '$1 $2 ').replace(/-/g, '−');
}

/* ================= Terme schön schreiben ================= */
const MI = '−';
const X2 = v => `${v}<sup>2</sup>`;
function glied(c, v, first) {
  const a = Math.abs(c), s = (a === 1 && v ? '' : fmt(a)) + v;
  return first ? (c < 0 ? MI : '') + s : (c < 0 ? ` ${MI} ` : ' + ') + s;
}
/* poly([3, X2('x')], [-5, 'x'], [2, '']) → „3x² − 5x + 2“ */
function poly(...gl) { let out = '', first = true; for (const [c, v] of gl) { if (!c) continue; out += glied(c, v, first); first = false; } return out || '0'; }
const pk = n => n < 0 ? `(${MI}${fmt(-n)})` : fmt(n);           // Zahl in einer Malaufgabe, negativ mit Klammer
const tgt = html => html.replace(/<sup>(\d)<\/sup>/g, '^$1');   // Anzeige → Eingabe-Schreibweise für die Bewertung
const sgn = () => pick([1, -1]);
const big = s => `<div class="big">${s}</div>`;
/* ---------- Grafische Tipps (Malte 4.11.2026): Bögen wie im Skript, Flächenbild, Bausteine ----------
   Die Grafik zeigt, WIE gerechnet wird (Malaufgaben, Felder, Bausteine) – nie das fertige Ergebnis. */
const BOGF = ['#2e5d9f', '#3f8f3a', '#7b4fa0', '#c0700f'];   // Skriptfarben: blau, grün, lila, orange
const NUMS = '①②③④';
// teile: Strings oder [index, text]; paare: [[i, j], …]; labels: Malaufgabe je Bogen (ohne Ergebnis)
function bogenGrafik(teile, paare, labels, vorspann = '') {
  const ausdr = teile.map(p => Array.isArray(p) ? `<span class="bt" data-i="${p[0]}">${p[1]}</span>` : p).join('');
  return `<div class="tippgrafik">${vorspann ? `<div class="vorsp">${vorspann}</div>` : ''}<div class="bogen" data-paare="${paare.map(p => p.join('-')).join(',')}"><svg class="bogsvg" aria-hidden="true"></svg><span class="ausdr">${ausdr}</span></div>
    <div class="boglab">${labels.map((l, i) => `<span style="color:${BOGF[i % 4]}">${NUMS[i]}&nbsp;${l}</span>`).join('')}</div></div>`;
}
// nach dem Einfügen ins Dokument aufrufen: zeichnet die Bögen über die markierten Teile
function zeichneBoegen(root) {
  root.querySelectorAll('.bogen').forEach(b => {
    const svg = b.querySelector('svg'), box = b.getBoundingClientRect();
    if (!box.width) return;
    svg.setAttribute('width', box.width); svg.setAttribute('height', box.height);
    const pos = i => { const e = b.querySelector(`.bt[data-i="${i}"]`).getBoundingClientRect(); return [e.left - box.left + e.width / 2, e.top - box.top]; };
    svg.innerHTML = b.dataset.paare.split(',').map((p, k) => {
      const [i, j] = p.split('-'), [x1, y] = pos(i), [x2] = pos(j), h = 18 + Math.min(40, Math.abs(x2 - x1) * 0.25) + k * 13, c = BOGF[k % 4];
      return `<path d="M${x1},${y - 2} Q${(x1 + x2) / 2},${y - 2 - 2 * h} ${x2},${y - 2}" fill="none" stroke="${c}" stroke-width="3"/>
        <circle cx="${(x1 + x2) / 2}" cy="${y - 2 - h}" r="11" fill="#fff" stroke="${c}" stroke-width="1.5"/><text x="${(x1 + x2) / 2}" y="${y - 2 - h}" text-anchor="middle" dominant-baseline="central" font-size="13" font-weight="700" fill="${c}">${k + 1}</text>`;
    }).join('');
  });
}
// Flächenbild (a + b)²: Seiten s1 (groß) und s2 (klein), vier Felder; Farben wie im Skript (a² blau, ab grün, b² orange)
function flaechenGrafik(s1, s2, felder, titel = '') {
  const A = 120, B = 62, x0 = 46, y0 = 34, F = [['#dbe7f7', '#2e5d9f'], ['#dcefd9', '#3f8f3a'], ['#dcefd9', '#3f8f3a'], ['#fde7c8', '#c0700f']];
  const r = [[x0, y0, A, A], [x0 + A, y0, B, A], [x0, y0 + A, A, B], [x0 + A, y0 + A, B, B]];
  const t = (x, y, s, o = '') => `<text x="${x}" y="${y}" text-anchor="middle" dominant-baseline="central" ${o}>${String(s).replace(/<sup>2<\/sup>/g, '²')}</text>`;   // im SVG kein <sup>
  return `<div class="tippgrafik">${titel ? `<div class="vorsp">${titel}</div>` : ''}<svg viewBox="0 0 ${x0 + A + B + 14} ${y0 + A + B + 10}" class="flsvg" font-family="system-ui,sans-serif" font-size="15" font-weight="700">
    ${r.map((q, i) => `<rect x="${q[0]}" y="${q[1]}" width="${q[2]}" height="${q[3]}" fill="${F[i][0]}" stroke="${F[i][1]}" stroke-width="2"/>${t(q[0] + q[2] / 2, q[1] + q[3] / 2, felder[i], `fill="${F[i][1]}"`)}`).join('')}
    ${t(x0 + A / 2, y0 - 14, s1)}${t(x0 + A + B / 2, y0 - 14, s2)}${t(x0 - 18, y0 + A / 2, s1)}${t(x0 - 18, y0 + A + B / 2, s2)}</svg></div>`;
}
// Bausteine (Ausklammern): jeder Teil in kleinste Malaufgaben zerlegt, Gemeinsames orange
const zerlege = n => { const f = []; for (let d = 2; n > 1; d++) while (n % d === 0) { f.push(String(d)); n /= d; } return f; };
function bausteinGrafik(teile) {   // teile: [{c: Zahl mit Vorzeichen, v: ['x', 'x', 'y']}]
  const listen = teile.map(t => [...zerlege(Math.abs(t.c)), ...t.v]);
  const rest = listen.slice(1).map(l => l.slice());
  const gem = listen[0].filter(s => rest.every(l => { const i = l.indexOf(s); if (i < 0) return false; l.splice(i, 1); return true; }));
  const zeile = (t, l) => { const g = gem.slice(); const name = poly([t.c, t.v.join('').replace(/(.)\1/, '$1<sup>2</sup>')]);
    return `<div class="bzeile"><span class="bname">${name}</span> = ${t.c < 0 ? MI + ' ' : ''}${l.map(s => { const i = g.indexOf(s); if (i >= 0) { g.splice(i, 1); return `<span class="bst gem">${s}</span>`; } return `<span class="bst">${s}</span>`; }).join(' · ')}</div>`; };
  return `<div class="tippgrafik">${teile.map((t, i) => zeile(t, listen[i])).join('')}<div class="vorsp">Orange = steckt in <b>beiden</b> Teilen → kommt vor die Klammer.</div></div>`;
}
/* Tipp-Grafik für Bruchgleichungen (Malte 5.11.2026): gemeinsamer Nenner mit der Vielfachen-Methode wie im Skript –
   größte Zahl in den Nennern, verdoppeln/verdreifachen bis alle passen, x einmal dazu. Kein kgV per Zerlegung. */
function korbGrafik(nenner, teile = null) {
  const zahl = n => { const m = String(n).match(/^(\d*)(x?)$/); return m[1] ? +m[1] : 1; }, mitX = nenner.some(n => /x/.test(n));
  const zs = nenner.map(zahl), g = Math.max(...zs); let k = 1; while (!zs.every(z => (g * k) % z === 0)) k++;
  const hn = g * k, hnT = `${hn === 1 && mitX ? '' : hn}${mitX ? 'x' : ''}`;
  const zeilen = nenner.map(n => `<div class="bzeile">Nenner <b>${n}</b></div>`);
  const schritt = zs.length > 1 ? `<div class="vorsp">Zahlen in den Nennern: ${zs.join(', ')} → größte Zahl ${g}${k > 1 ? `, passt nicht überall → ${k} · ${g} = ${hn}` : ' – die anderen passen hinein ✓'}</div>` : '';
  return `<div class="tippgrafik">${zeilen.join('')}${schritt}${mitX ? '<div class="vorsp">x steht im Nenner → x kommt <b>einmal</b> dazu.</div>' : ''}
    <div class="korbbox"><span class="klbl">Gemeinsamer Nenner</span> <b>${hnT}</b></div>
    <div class="vorsp">Dann <b>jeden Teil</b> mal den gemeinsamen Nenner – auch die Zahl ohne Bruch. Er kommt in den Zähler, dann kürzen.</div>
    ${teile ? `<div class="teilz">${teile.map((x, i) => `${i === teile.length - 1 ? '= ' : i ? '+ ' : ''}<span class="bst${x === 'Zahl' ? ' gem' : ''}">${x}</span> · <b>${hnT}</b>`).join(' ')}</div><div class="vorsp">Orange: Auch die Zahlen ohne Bruch werden mal genommen!</div>` : ''}</div>`;
}
const KORB = { bruchX: [['x'], ['Bruch', 'Zahl', 'Zahl']], bruchBeide: [['x'], ['Bruch', 'Zahl', 'Bruch']], bruch2x: [['2x'], ['Bruch', 'Zahl', 'Zahl']], bruchMix: [['x', '2x']] };
// vier Bögen für (p + a)(q + b) – Reihenfolge wie im Skript: ① blau ② grün ③ lila ④ orange
function vierBoegen(p, a, q, b, nachsatz = '', vorspann = '') {
  const op = z => z < 0 ? ` ${MI} ` : ' + ';
  const g = bogenGrafik(['(', [0, p], op(a), [1, Math.abs(a)], ') · (', [2, q], op(b), [3, Math.abs(b)], ')'], [[0, 2], [0, 3], [1, 2], [1, 3]],
    [`${p} · ${q}`, `${p} · ${pk(b)}`, `${pk(a)} · ${q}`, `${pk(a)} · ${pk(b)}`], vorspann);
  return nachsatz ? g.replace(/<\/div>$/, `<div class="vorsp">${nachsatz}</div></div>`) : g;
}
const termTask = (o) => Object.assign({ type: 'term', target: tgt(o.ansHtml) }, o);

/* ---------- Figuren (SVG): Punkte in Einheiten, y nach oben. Beschriftungen mit weißem Rand, rechter Winkel als Bogen mit Punkt ---------- */
const FB = { g: '#2e5d9f', h: '#c0700f', c: '#3f8f3a', r: '#6b5a45', f: '#f1e6d2', t: '#333' };
function figur(pts, o = {}) {
  const all = pts.concat(o.extraPts || []);
  const xs = all.map(p => p[0]), ys = all.map(p => p[1]);
  const x0 = Math.min(...xs), x1 = Math.max(...xs), y0 = Math.min(...ys), y1 = Math.max(...ys);
  const K = Math.min(34, 300 / Math.max(1, x1 - x0), 190 / Math.max(1, y1 - y0)), M = 36, MX = 92;   // seitlich Platz für Beschriftungen
  const X = x => MX + (x - x0) * K, Y = y => M + (y1 - y) * K, W = (x1 - x0) * K + 2 * MX, H = (y1 - y0) * K + 2 * M;
  let s = `<svg class="fig" viewBox="0 0 ${W.toFixed(0)} ${H.toFixed(0)}" style="max-width:${Math.min(420, W).toFixed(0)}px" xmlns="http://www.w3.org/2000/svg">`;
  const T = (x, y, t, c = FB.t, a = 'middle') => `<text x="${x.toFixed(1)}" y="${(y + 6).toFixed(1)}" font-size="17" font-weight="700" fill="${c}" text-anchor="${a}" style="paint-order:stroke;stroke:#fff;stroke-width:5px;stroke-linejoin:round">${t}</text>`;
  (o.teile || []).forEach((tp, k) => { s += `<polygon points="${tp.map(p => X(p[0]) + ',' + Y(p[1])).join(' ')}" fill="${['#cfe3f5', '#f6dcb8', '#d9ecd0'][k % 3]}" stroke="${FB.r}" stroke-width="1.5" stroke-dasharray="5 4"/>`; });
  s += `<polygon points="${pts.map(p => X(p[0]) + ',' + Y(p[1])).join(' ')}" fill="${o.teile ? 'none' : FB.f}" stroke="${FB.r}" stroke-width="2.5"/>`;
  const cx = pts.reduce((a, p) => a + p[0], 0) / pts.length, cy = pts.reduce((a, p) => a + p[1], 0) / pts.length;
  (o.seiten || []).forEach(([i, j, txt, col]) => {
    const P = pts[i], Q = pts[j], m = [(P[0] + Q[0]) / 2, (P[1] + Q[1]) / 2];
    let n = [-(Q[1] - P[1]), Q[0] - P[0]]; const l = Math.hypot(...n); n = [n[0] / l, n[1] / l];
    if ((cx - m[0]) * n[0] + (cy - m[1]) * n[1] > 0) n = [-n[0], -n[1]];
    if (col) s += `<line x1="${X(P[0])}" y1="${Y(P[1])}" x2="${X(Q[0])}" y2="${Y(Q[1])}" stroke="${col}" stroke-width="5"/>`;
    const a = n[0] < -0.3 ? 'end' : n[0] > 0.3 ? 'start' : 'middle';
    s += T(X(m[0] + 0.5 * n[0]), Y(m[1] + 0.5 * n[1]), txt, col || FB.t, a);
  });
  (o.hoehen || []).forEach(([P, F, txt, opt = {}]) => {
    s += `<line x1="${X(P[0])}" y1="${Y(P[1])}" x2="${X(F[0])}" y2="${Y(F[1])}" stroke="${opt.col || FB.h}" stroke-width="3" stroke-dasharray="7 5"/>`;
    if (!opt.ohneWinkel) { const u = [P[0] - F[0], P[1] - F[1]], lu = Math.hypot(...u), e = [u[0] / lu, u[1] / lu], v = opt.v || [1, 0], r = 0.55;
      const p1 = [F[0] + r * v[0], F[1] + r * v[1]], p2 = [F[0] + r * e[0], F[1] + r * e[1]], cr = e[0] * v[1] - e[1] * v[0];
      s += `<path d="M ${X(p1[0])} ${Y(p1[1])} A ${r * K} ${r * K} 0 0 ${cr > 0 ? 1 : 0} ${X(p2[0])} ${Y(p2[1])}" fill="none" stroke="${opt.col || FB.h}" stroke-width="2.4"/>`;
      s += `<circle cx="${X(F[0] + 0.24 * (e[0] + v[0]))}" cy="${Y(F[1] + 0.24 * (e[1] + v[1]))}" r="3" fill="${opt.col || FB.h}"/>`; }
    if (txt) s += T(X((P[0] + F[0]) / 2 + (opt.dx ?? 0.25)), Y((P[1] + F[1]) / 2), txt, opt.col || FB.h, 'start');
  });
  (o.linien || []).forEach(([P, Q, col]) => { s += `<line x1="${X(P[0])}" y1="${Y(P[1])}" x2="${X(Q[0])}" y2="${Y(Q[1])}" stroke="${col}" stroke-width="5"/>`; });
  (o.verl || []).forEach(([P, Q]) => { s += `<line x1="${X(P[0])}" y1="${Y(P[1])}" x2="${X(Q[0])}" y2="${Y(Q[1])}" stroke="#555" stroke-width="2" stroke-dasharray="6 5"/>`; });
  (o.texte || []).forEach(([x, y, t, c]) => { s += T(X(x), Y(y), t, c || FB.t); });
  return s + '</svg>';
}
const kz = x => fmt(x);
const qf = (txt, svg) => `${txt}<div class="figbox">${svg}</div>`;
const FR = (z, n) => frac(z, n);

/* ---------- Aufgabengeneratoren (Kl. 8 RS, II Umfang und Flächeninhalt, 27.11.2026) ----------
   Jede Aufgabe: { title, q, type: 'num'|'mc', ans, post (Einheit), hint, sol:[Schritte – ein Schritt pro Zeile] }
   Eigene Aufgaben (Copyright): nur Aufgabentypen aus dem Unterricht, keine Buchaufgaben. Drachen/Raute nicht behandelt → nicht enthalten. */
/* Zwei gleiche Figuren (die zweite gedreht) ergeben ein Parallelogramm – Bild für die Herleitungs-Aufgaben */
function herleitBild(f1, f2, o) {
  const top = o.h, mitte = f => [f.reduce((x, p) => x + p[0], 0) / f.length, f.reduce((x, p) => x + p[1], 0) / f.length];
  const m1 = mitte(f1), m2 = mitte(f2);
  const pts = o.dreieck ? [[0, 0], [o.g, 0], [o.g + o.l, top], [o.l, top]] : [[0, 0], [o.a + o.c, 0], [o.a + o.c + o.l, top], [o.l, top]];
  const nr = [[m1[0] + 0.5, m1[1], '1', FB.r], [m2[0], m2[1], '2', FB.r]];
  const texte = o.dreieck
    ? [[o.g / 2, -0.75, 'g', FB.g], [o.l + o.g / 2, top + 0.75, 'g', FB.g], ...nr]
    : [[o.a / 2, -0.75, 'a', FB.g], [o.a + o.c / 2, -0.75, 'c', FB.c], [o.l + o.c / 2, top + 0.75, 'c', FB.c], [o.l + o.c + o.a / 2, top + 0.75, 'a', FB.g], ...nr];
  const linien = o.dreieck
    ? [[[0, 0], [o.g, 0], FB.g], [[o.l, top], [o.l + o.g, top], FB.g]]
    : [[[0, 0], [o.a, 0], FB.g], [[o.a, 0], [o.a + o.c, 0], FB.c], [[o.l, top], [o.l + o.c, top], FB.c], [[o.l + o.c, top], [o.l + o.c + o.a, top], FB.g]];
  return figur(pts, { teile: [f1, f2], linien, hoehen: [[[o.l, top], [o.l, 0], 'h', { dx: 0.25 }]], texte, extraPts: [[0, -1.1], [0, top + 1.1]] });
}
const G = {
  /* ===== II.1 Rechteck und Quadrat ===== */
  rechteckA() {
    const a = R(4, 12), b = R(2, a - 1), e = pick(['m', 'cm']);
    return { title: 'Flächeninhalt eines Rechtecks', q: qf(`Ein rechteckiges Beet ist <b>${a} ${e}</b> lang und <b>${b} ${e}</b> breit. Berechne den <b>Flächeninhalt</b>.`,
      figur([[0, 0], [a, 0], [a, b], [0, b]], { seiten: [[0, 1, `${a} ${e}`, FB.g], [1, 2, `${b} ${e}`, FB.h]] })),
      type: 'num', ans: a * b, pre: 'A =', post: e + '²', hint: 'Flächeninhalt = Länge mal Breite. Die Einheit wird zu ' + e + '².',
      sol: ['A = a · b', `A = ${a} ${e} · ${b} ${e}`, `A = ${a * b} ${e}²`] };
  },
  rechteckU() {
    const a = R(4, 12), b = R(2, a - 1), e = pick(['m', 'cm']), quadrat = rand() < .3;
    const bb = quadrat ? a : b;
    return { title: quadrat ? 'Umfang eines Quadrats' : 'Umfang eines Rechtecks', q: qf(quadrat ? `Ein quadratischer Sandkasten hat die Seitenlänge <b>${a} ${e}</b>. Wie viel Zaun braucht man rundherum? Berechne den <b>Umfang</b>.` : `Ein rechteckiges Beet ist <b>${a} ${e}</b> lang und <b>${b} ${e}</b> breit. Wie viel Zaun braucht man rundherum? Berechne den <b>Umfang</b>.`,
      figur([[0, 0], [a, 0], [a, bb], [0, bb]], { seiten: [[0, 1, `${a} ${e}`, FB.g], [1, 2, `${bb} ${e}`, FB.h]] })),
      type: 'num', ans: 2 * a + 2 * bb, pre: 'U =', post: e, hint: 'Umfang = alle vier Seiten zusammen: 2 · a + 2 · b.',
      sol: quadrat ? ['U = 4 · a', `U = 4 · ${a} ${e}`, `U = ${4 * a} ${e}`] : ['U = 2 · a + 2 · b', `U = 2 · ${a} ${e} + 2 · ${b} ${e}`, `U = ${2 * a} ${e} + ${2 * b} ${e}`, `U = ${2 * a + 2 * b} ${e}`] };
  },
  einheit() {
    const t = pick([['m²', 'dm²', 100], ['dm²', 'cm²', 100], ['dm²', 'm²', 0.01], ['cm²', 'dm²', 0.01], ['m²', 'cm²', 10000]]);
    const x = t[2] >= 1 ? pick([2, 3, 5, 7, 2.5, 4.5]) : pick([300, 500, 800, 1200, 250, 450]);
    const L = Math.round(x * t[2] * 1000) / 1000, runter = t[2] > 1;
    return { title: 'Flächeneinheiten umrechnen', q: `Rechne um.${big(`${kz(x)} ${t[0]} = ? ${t[1]}`)}`, type: 'num', ans: L, post: t[1],
      hint: 'Von einer Flächeneinheit zur nächsten kleineren: mal 100. Zur nächsten größeren: durch 100. Von m² nach cm² sind es zwei Stufen.',
      sol: [`${kz(x)} ${t[0]} = ${kz(x)} ${runter ? '·' : ':'} ${t[2] >= 1 ? kz(t[2]) : kz(1 / t[2])} ${t[1]}`, `${kz(x)} ${t[0]} = ${kz(L)} ${t[1]}`] };
  },
  /* ===== II.2a Parallelogramm ===== */
  paraA() {
    const a = R(5, 11), h = R(2, 6), s = R(1, 3), b = Math.round(Math.hypot(s, h) * 10) / 10, e = pick(['m', 'cm']);
    return { title: 'Flächeninhalt eines Parallelogramms', q: qf(`Das Parallelogramm hat die Seite <b>a = ${a} ${e}</b>, die Höhe <b>h<sub>a</sub> = ${h} ${e}</b> und die schräge Seite <b>b = ${kz(b)} ${e}</b>. Berechne den <b>Flächeninhalt</b>.`,
      figur([[0, 0], [a, 0], [a + s, h], [s, h]], { seiten: [[0, 1, `a = ${a} ${e}`, FB.g], [1, 2, `b = ${kz(b)} ${e}`]], hoehen: [[[s, h], [s, 0], `h<tspan baseline-shift="sub" font-size="12">a</tspan> = ${h} ${e}`]] })),
      type: 'num', ans: a * h, pre: 'A =', post: e + '²', hint: 'Seite mal ihre Höhe – die schräge Seite b brauchst du für den Flächeninhalt nicht.',
      sol: ['A = a · h<sub>a</sub>', `A = ${a} ${e} · ${h} ${e}`, `A = ${a * h} ${e}²`] };
  },
  paraU() {
    const [h, s, b] = pick([[4, 3, 5], [3, 4, 5], [8, 6, 10], [12, 5, 13], [6, 8, 10]]), a = R(b + 1, b + 7), e = pick(['m', 'cm']);
    return { title: 'Umfang eines Parallelogramms', q: qf(`Das Parallelogramm hat die Seiten <b>a = ${a} ${e}</b> und <b>b = ${b} ${e}</b> und die Höhe <b>h<sub>a</sub> = ${h} ${e}</b>. Berechne den <b>Umfang</b>.`,
      figur([[0, 0], [a, 0], [a + s, h], [s, h]], { seiten: [[0, 1, `a = ${a} ${e}`, FB.g], [1, 2, `b = ${b} ${e}`]], hoehen: [[[s, h], [s, 0], `${h} ${e}`]] })),
      type: 'num', ans: 2 * a + 2 * b, pre: 'U =', post: e, hint: 'Für den Umfang brauchst du die Seiten, nicht die Höhe: U = 2 · a + 2 · b.',
      sol: ['U = 2 · a + 2 · b', `U = 2 · ${a} ${e} + 2 · ${b} ${e}`, `U = ${2 * a + 2 * b} ${e}`] };
  },
  /* ===== II.2b Höhe erkennen ===== */
  hoeheMC() {
    const aussen = rand() < .5, a = aussen ? R(3, 4) : R(6, 8), h = R(4, 5), s = aussen ? R(a + 1, a + 2) : R(2, 3);
    const P = [s, h], F = [s, 0];
    const kand = shuffle([[F, 'senk'], [[s - 2.2, 0], 'schief'], [[s + 2.3, 0], 'schief2']]);
    const nr = ['1', '2', '3'];
    const hoehen = kand.map(([Q, art], i) => [P, [P[0] + 0.62 * (Q[0] - P[0]), 0.38 * h], '', { ohneWinkel: true, col: ['#2e5d9f', '#3f8f3a', '#7b4fa0'][i] }]).concat(kand.map(([Q], i) => [[P[0] + 0.62 * (Q[0] - P[0]), 0.38 * h], Q, '', { ohneWinkel: true, col: ['#2e5d9f', '#3f8f3a', '#7b4fa0'][i] }]));
    const nummern = kand.map(([Q], i) => [P[0] + 0.55 * (Q[0] - P[0]) + (Q[0] < P[0] ? -0.35 : Q[0] > P[0] ? 0.35 : 0.3), 0.45 * h, nr[i], ['#2e5d9f', '#3f8f3a', '#7b4fa0'][i]]);
    const verl = aussen ? [[[a, 0], [s + 2.6, 0]]] : [];
    const richtig = nr[kand.findIndex(k => k[1] === 'senk')];
    return { title: 'Welche Strecke ist die Höhe?', q: qf(`Drei Strecken gehen von der oberen Ecke zur (verlängerten) Seite a. Welche Strecke ist die <b>Höhe h<sub>a</sub></b>?`,
      figur([[0, 0], [a, 0], [a + s, h], [s, h]], { seiten: [[0, 1, 'a', FB.g]], hoehen, verl, texte: nummern, extraPts: [[s + 2.6, 0], [s - 2.4, 0]] })),
      type: 'mc', options: nr.map(n => `Strecke ${n}`), ans: `Strecke ${richtig}`,
      hint: 'Die Höhe steht senkrecht (rechter Winkel) auf der Seite a – sie ist die kürzeste Strecke. Liegt die Ecke nicht über a, wird a verlängert.',
      sol: [`Strecke ${richtig} steht senkrecht auf a.`, aussen ? 'Hier liegt die Höhe außerhalb – a ist verlängert.' : 'Sie ist die kürzeste Verbindung zur Seite a.'] };
  },
  /* ===== II.3a Dreieck ===== */
  dreieckA() {
    const g = R(6, 12), h = R(3, Math.min(8, g - 1)), sp = R(1, g - 1), e = pick(['m', 'cm']), A = g * h / 2;
    const s1 = Math.round(Math.hypot(sp, h) * 10) / 10, s2 = Math.round(Math.hypot(g - sp, h) * 10) / 10;
    return { title: 'Flächeninhalt eines Dreiecks', q: qf(`Das Dreieck hat die Grundseite <b>g = ${g} ${e}</b> und die Höhe <b>h = ${h} ${e}</b>. Die anderen Seiten sind ${kz(s1)} ${e} und ${kz(s2)} ${e} lang. Berechne den <b>Flächeninhalt</b>.`,
      figur([[0, 0], [g, 0], [sp, h]], { seiten: [[0, 1, `g = ${g} ${e}`, FB.g], [0, 2, `${kz(s1)} ${e}`], [1, 2, `${kz(s2)} ${e}`]], hoehen: [[[sp, h], [sp, 0], `h = ${h} ${e}`]] })),
      type: 'num', ans: A, pre: 'A =', post: e + '²', hint: 'Grundseite mal Höhe, dann durch 2. Die schrägen Seiten brauchst du nicht.',
      sol: [`A = ${FR('g · h', '2')}`, `A = ${FR(`${g} ${e} · ${h} ${e}`, '2')}`, `A = ${FR(`${g * h} ${e}²`, '2')}`, `A = ${kz(A)} ${e}²`] };
  },
  dreieckU() {
    const f = pick([1, 1, 2]), [a, b, c] = pick([[5, 6, 7], [4, 7, 9], [6, 6, 8], [3, 4, 5], [7, 8, 10]]).map(x => x * f), e = pick(['m', 'cm']), h = Math.max(2, Math.round(c / 2));
    return { title: 'Umfang eines Dreiecks', q: `Ein Dreieck hat die Seiten <b>${a} ${e}</b>, <b>${b} ${e}</b> und <b>${c} ${e}</b>. Die Höhe auf die längste Seite ist ${h} ${e}. Berechne den <b>Umfang</b>.`,
      type: 'num', ans: a + b + c, pre: 'U =', post: e, hint: 'Umfang: alle drei Seiten addieren. Die Höhe gehört nicht dazu.',
      sol: ['U = a + b + c', `U = ${a} ${e} + ${b} ${e} + ${c} ${e}`, `U = ${a + b + c} ${e}`] };
  },
  /* ===== II.3b Seite und ihre Höhe ===== */
  dreieckRecht() {
    const [a, b, c] = pick([[6, 8, 10], [5, 12, 13], [9, 12, 15], [8, 15, 17], [3, 4, 5]]), e = pick(['m', 'cm']);
    return { title: 'Rechtwinkliges Dreieck', q: qf(`Das Dreieck ist rechtwinklig. Die Seiten am rechten Winkel sind <b>${a} ${e}</b> und <b>${b} ${e}</b> lang, die lange Seite <b>${c} ${e}</b>. Berechne den <b>Flächeninhalt</b>.`,
      figur([[0, 0], [b, 0], [0, a]], { seiten: [[0, 1, `${b} ${e}`, FB.g], [0, 2, `${a} ${e}`, FB.h], [1, 2, `${c} ${e}`]], hoehen: [[[0, a], [0, 0], '', { ohneWinkel: false, col: FB.h }]] })),
      type: 'num', ans: a * b / 2, pre: 'A =', post: e + '²', hint: 'Im rechtwinkligen Dreieck ist die eine Seite am rechten Winkel die Höhe zur anderen. Die lange Seite brauchst du nicht.',
      sol: [`A = ${FR('g · h', '2')}`, `A = ${FR(`${b} ${e} · ${a} ${e}`, '2')}`, `A = ${FR(`${a * b} ${e}²`, '2')}`, `A = ${kz(a * b / 2)} ${e}²`] };
  },
  dreieckSeite() {
    const nm = pick(['b', 'c', 'a']), g = R(6, 10), h = R(3, 6), e = pick(['cm', 'm']), th = pick([0.35, 0.5, -0.35]), t = pick([0.3, 0.5, 0.7]);
    const u = [Math.cos(th), Math.sin(th)], n = [-Math.sin(th), Math.cos(th)], P1 = [g * u[0], g * u[1]], F = [t * P1[0], t * P1[1]], S = [F[0] + h * n[0], F[1] + h * n[1]];
    const anders = Math.round(Math.hypot(S[0], S[1]) * 10) / 10;
    return { title: 'Seite und ihre Höhe', q: qf(`Im Dreieck ist die Seite <b>${nm} = ${g} ${e}</b> und ihre Höhe <b>h<sub>${nm}</sub> = ${h} ${e}</b>. Eine andere Seite ist ${kz(anders)} ${e} lang. Berechne den <b>Flächeninhalt</b>.`,
      figur([[0, 0], P1, S], { seiten: [[0, 1, `${nm} = ${g} ${e}`, FB.g], [0, 2, `${kz(anders)} ${e}`]], hoehen: [[S, F, `h<tspan baseline-shift="sub" font-size="12">${nm}</tspan> = ${h} ${e}`, { v: u }]] })),
      type: 'num', ans: g * h / 2, pre: 'A =', post: e + '²', hint: `Nimm die Seite ${nm} und genau ihre Höhe h${nm}: Seite mal ihre Höhe, durch 2. Die andere Seite brauchst du nicht.`,
      sol: [`A = ${FR(`${nm} · h<sub>${nm}</sub>`, '2')}`, `A = ${FR(`${g} ${e} · ${h} ${e}`, '2')}`, `A = ${FR(`${g * h} ${e}²`, '2')}`, `A = ${kz(g * h / 2)} ${e}²`] };
  },
  /* ===== II.4a Trapez ===== */
  trapezA() {
    const rw = rand() < .4, a = R(6, 12), c = R(2, a - 2), h = R(2, 6), l = rw ? 0 : R(1, a - c - 1), e = pick(['m', 'cm']), A = (a + c) * h / 2;
    const sch = rw ? h : Math.round(Math.hypot(l, h) * 10) / 10;
    return { title: rw ? 'Rechtwinkliges Trapez' : 'Flächeninhalt eines Trapezes', q: qf(`${rw ? 'Auch das ist ein Trapez – ein rechtwinkliges. ' : ''}Es hat <b>a = ${a} ${e}</b>, <b>c = ${c} ${e}</b> und <b>h = ${h} ${e}</b>${rw ? '' : `, ein Schenkel ist ${kz(sch)} ${e} lang`}. Berechne den <b>Flächeninhalt</b>.`,
      figur([[0, 0], [a, 0], [l + c, h], [l, h]], { seiten: [[0, 1, `a = ${a} ${e}`, FB.g], [3, 2, `c = ${c} ${e}`, FB.c]].concat(rw ? [] : [[0, 3, `${kz(sch)} ${e}`]]), hoehen: [[[l, h], [l, 0], `h = ${h} ${e}`]] })),
      type: 'num', ans: A, pre: 'A =', post: e + '²', hint: 'Erst a + c addieren (Klammer), dann mal h, dann durch 2. Die Schenkel brauchst du nicht.',
      sol: [`A = ${FR('(a + c) · h', '2')}`, `A = ${FR(`(${a} ${e} + ${c} ${e}) · ${h} ${e}`, '2')}`, `A = ${FR(`${a + c} ${e} · ${h} ${e}`, '2')}`, `A = ${FR(`${(a + c) * h} ${e}²`, '2')}`, `A = ${kz(A)} ${e}²`] };
  },
  trapezU() {
    const h = 4, [l, d] = pick([[3, 5], [0, 4]]), [r, b] = pick([[3, 5], [3, 5], [0, 4]]), c = R(3, 6), a = c + l + r, e = pick(['m', 'cm']);
    return { title: 'Umfang eines Trapezes', q: `Ein Trapez hat die Seiten <b>a = ${a} ${e}</b>, <b>b = ${b} ${e}</b>, <b>c = ${c} ${e}</b>, <b>d = ${d} ${e}</b> und die Höhe ${h} ${e}. Berechne den <b>Umfang</b>.`,
      type: 'num', ans: a + b + c + d, pre: 'U =', post: e, hint: 'Alle vier Seiten addieren – die Höhe gehört nicht dazu.',
      sol: ['U = a + b + c + d', `U = ${a} ${e} + ${b} ${e} + ${c} ${e} + ${d} ${e}`, `U = ${a + b + c + d} ${e}`] };
  },
  /* ===== Herleiten aus dem Parallelogramm (27.11.2026, Malte: vor allem beim Trapez – warum a + c, warum h bleibt, warum durch 2).
     Mehrere Fragen je Figur, je 4 Antworten in zufälliger Reihenfolge; die falschen Antworten sind typische Fehlvorstellungen. ===== */
  herleitTrapez() {
    const rw = rand() < .3, e = pick(['cm', 'm']);
    let a, c, h, l;
    do { a = R(6, 11); c = R(2, a - 3); h = 2 * R(2, 4); l = rw ? 0 : R(1, a - c - 1); } while (h === a + c || h === a || h === c || 2 * h === a + c);
    const bild = herleitBild([[0, 0], [a, 0], [l + c, h], [l, h]], [[a, 0], [a + c, 0], [a + c + l, h], [l + c, h]], { a, c, h, l, e });
    const fig = rw ? `Zwei gleiche <b>rechtwinklige</b> Trapeze mit <b>a = ${a} ${e}</b>, <b>c = ${c} ${e}</b> und <b>h = ${h} ${e}</b>. Das zweite ist gedreht und liegt daneben. Zusammen ergeben sie ein Rechteck – auch das ist ein Parallelogramm.`
      : `Zwei gleiche Trapeze mit <b>a = ${a} ${e}</b>, <b>c = ${c} ${e}</b> und <b>h = ${h} ${e}</b>. Das zweite ist gedreht und liegt daneben. Zusammen ergeben sie ein Parallelogramm.`;
    const P = (a + c) * h;
    const V = [
      () => ({ f: 'Wie lang ist die <b>Grundseite des Parallelogramms</b>?', ok: `${a + c} ${e}`, no: [`${a} ${e}`, `${a - c} ${e}`, `${2 * a} ${e}`],
        hint: 'Schau unten auf die Grundseite: Dort liegt die Seite a des ersten Trapezes und daneben die Seite c des gedrehten Trapezes.',
        sol: ['Grundseite = a + c', `Grundseite = ${a} ${e} + ${c} ${e}`, `Grundseite = ${a + c} ${e}`] }),
      () => ({ f: 'Wie <b>hoch</b> ist das Parallelogramm?', ok: `${h} ${e}`, no: [`${2 * h} ${e}`, `${h / 2} ${e}`, `${a + c} ${e}`],
        hint: 'Die Trapeze liegen nebeneinander, nicht übereinander. Wird die Figur dadurch höher?',
        sol: ['Die Trapeze liegen nebeneinander.', `Das Parallelogramm ist genauso hoch wie ein Trapez: h = ${h} ${e}.`] }),
      () => ({ f: 'Wie groß ist der <b>Flächeninhalt eines Trapezes</b>?', ok: `${kz(P / 2)} ${e}²`, no: [`${P} ${e}²`, `${kz(P / 4)} ${e}²`, `${kz([P, P / 2, P / 4].includes(a * c * h / 2) ? 2 * P : a * c * h / 2)} ${e}²`],
        hint: 'Rechne zuerst den Flächeninhalt des ganzen Parallelogramms: Grundseite (a + c) mal Höhe. Ein Trapez ist die Hälfte davon.',
        sol: ['Parallelogramm: A = (a + c) · h', `Parallelogramm: A = ${a + c} ${e} · ${h} ${e}`, `Parallelogramm: A = ${P} ${e}²`, `Ein Trapez ist die Hälfte: A = ${kz(P / 2)} ${e}²`] }),
      () => ({ f: 'Warum ist die Grundseite des Parallelogramms <b>a + c</b> lang?', ok: 'Das zweite Trapez ist gedreht. Darum liegt unten seine Seite c neben der Seite a.',
        no: ['Beim Trapez zählt man immer alle Seiten zusammen.', 'Die Seiten a und c sind gleich lang.', 'Die beiden Schenkel sind zusammen so lang wie a + c.'],
        hint: 'Fahre im Bild die Grundseite von links nach rechts ab. Zu welchem Trapez gehört welches Stück?',
        sol: ['Linkes Stück der Grundseite: Seite a vom ersten Trapez.', 'Rechtes Stück: Seite c vom gedrehten Trapez.', 'Zusammen: a + c.'] }),
      () => ({ f: 'Warum steht in der Trapez-Formel <b>„durch 2“</b>?', ok: 'Das Parallelogramm besteht aus zwei gleichen Trapezen. Ein Trapez ist die Hälfte davon.',
        no: ['Das Trapez hat zwei parallele Seiten.', 'Im Trapez ist die Höhe nur halb so lang.', 'Ein Trapez hat zwei Schenkel.'],
        hint: 'Wie viele Trapeze stecken im Parallelogramm?',
        sol: ['Im Parallelogramm stecken zwei gleiche Trapeze.', 'Parallelogramm: (a + c) · h', `Ein Trapez: ${FR('(a + c) · h', '2')}`] }),
      () => ({ f: 'Warum steht <b>a + c</b> in der Formel in einer <b>Klammer</b>?', ok: 'Erst a + c ergibt die ganze Grundseite. Die ganze Grundseite wird mit h multipliziert.',
        no: ['Ohne Klammer wäre die Formel zu lang.', 'Nur die Seite c wird mit h multipliziert.', 'Die Klammer bedeutet, dass man a durch c teilt.'],
        hint: 'Im Parallelogramm rechnet man Grundseite mal Höhe. Wie lang ist hier die Grundseite?',
        sol: ['Grundseite des Parallelogramms = a + c', 'Die ganze Grundseite mal h: (a + c) · h', 'Ohne Klammer würde nur c mit h multipliziert.'] }),
      () => ({ f: 'Welche Formel gibt den Flächeninhalt <b>eines</b> Trapezes an?', ok: `A = ${FR('(a + c) · h', '2')}`, no: ['A = (a + c) · h', `A = ${FR('a · c · h', '2')}`, `A = ${FR('(a + c) · h', '4')}`],
        hint: 'Parallelogramm: Grundseite (a + c) mal Höhe h. Ein Trapez ist die Hälfte.',
        sol: ['Parallelogramm: A = (a + c) · h', `Ein Trapez: A = ${FR('(a + c) · h', '2')}`] }),
    ];
    const v = pick(V)();
    return { title: 'Trapez-Formel herleiten', q: qf(`${fig} ${v.f}`, bild), type: 'mc', options: shuffle([v.ok, ...v.no]), ans: v.ok, hint: v.hint, sol: v.sol };
  },
  herleitDreieck() {
    const e = pick(['cm', 'm']);
    let g, h, sp;
    do { g = R(5, 10); h = 2 * R(2, 4); sp = R(1, g - 1); } while (h === g || 2 * h === g || h === 2 * g);
    const bild = herleitBild([[0, 0], [g, 0], [sp, h]], [[g, 0], [g + sp, h], [sp, h]], { g, h, l: sp, e, dreieck: true });
    const fig = `Zwei gleiche Dreiecke mit <b>g = ${g} ${e}</b> und <b>h = ${h} ${e}</b>. Das zweite ist gedreht und liegt daneben. Zusammen ergeben sie ein Parallelogramm.`;
    const P = g * h;
    const V = [
      () => ({ f: 'Wie groß ist der <b>Flächeninhalt eines Dreiecks</b>?', ok: `${kz(P / 2)} ${e}²`, no: [`${P} ${e}²`, `${2 * P} ${e}²`, `${kz(P / 4)} ${e}²`],
        hint: 'Rechne zuerst das Parallelogramm: g mal h. Ein Dreieck ist die Hälfte davon.',
        sol: ['Parallelogramm: A = g · h', `Parallelogramm: A = ${g} ${e} · ${h} ${e}`, `Parallelogramm: A = ${P} ${e}²`, `Ein Dreieck ist die Hälfte: A = ${kz(P / 2)} ${e}²`] }),
      () => ({ f: 'Wie lang ist die <b>Grundseite des Parallelogramms</b>?', ok: `${g} ${e}`, no: [`${2 * g} ${e}`, `${g + h} ${e}`, `${kz(g / 2)} ${e}`],
        hint: 'Schau unten auf die Grundseite: Sie gehört nur zum ersten Dreieck.',
        sol: ['Unten liegt nur die Grundseite des ersten Dreiecks.', `Grundseite = g = ${g} ${e}`] }),
      () => ({ f: 'Warum steht in der Dreieck-Formel <b>„durch 2“</b>?', ok: 'Zwei gleiche Dreiecke ergeben ein Parallelogramm. Ein Dreieck ist die Hälfte davon.',
        no: ['Ein Dreieck hat drei Seiten.', 'Die Höhe steht immer genau in der Mitte.', 'Man rechnet g und h zusammen und halbiert.'],
        hint: 'Wie viele Dreiecke stecken im Parallelogramm?',
        sol: ['Im Parallelogramm stecken zwei gleiche Dreiecke.', 'Parallelogramm: g · h', `Ein Dreieck: ${FR('g · h', '2')}`] }),
      () => ({ f: 'Welche Formel gibt den Flächeninhalt <b>eines</b> Dreiecks an?', ok: `A = ${FR('g · h', '2')}`, no: ['A = g · h', 'A = 2 · g · h', `A = ${FR('g + h', '2')}`],
        hint: 'Parallelogramm: g mal h. Ein Dreieck ist die Hälfte.',
        sol: ['Parallelogramm: A = g · h', `Ein Dreieck: A = ${FR('g · h', '2')}`] }),
    ];
    const v = pick(V)();
    return { title: 'Dreieck-Formel herleiten', q: qf(`${fig} ${v.f}`, bild), type: 'mc', options: shuffle([v.ok, ...v.no]), ans: v.ok, hint: v.hint, sol: v.sol };
  },
  /* ===== Rückwärts: aus dem Flächeninhalt eine Größe ===== */
  rueckRechteck() {
    const a = R(4, 12), b = R(2, 9), e = pick(['m', 'cm']), A = a * b;
    return { title: 'Rückwärts: Rechteck', q: `Ein rechteckiges Beet hat einen Flächeninhalt von <b>${A} ${e}²</b> und ist <b>${a} ${e}</b> lang. Berechne die <b>Breite b</b>.`,
      type: 'num', ans: b, pre: 'b =', post: e, hint: 'A = a · b. Setze ein und rechne rückwärts: Flächeninhalt geteilt durch die Länge.',
      sol: ['A = a · b', `${A} ${e}² = ${a} ${e} · b`, `b = ${A} ${e}² : ${a} ${e}`, `b = ${b} ${e}`] };
  },
  rueckPara() {
    const a = R(4, 12), h = R(2, 9), e = pick(['m', 'cm']), A = a * h;
    return { title: 'Rückwärts: Parallelogramm', q: `Ein Parallelogramm hat einen Flächeninhalt von <b>${A} ${e}²</b> und die Seite <b>a = ${a} ${e}</b>. Berechne die <b>Höhe h<sub>a</sub></b>.`,
      type: 'num', ans: h, pre: 'h<sub>a</sub> =', post: e, hint: 'A = a · h_a. Rückwärts: Flächeninhalt geteilt durch a.',
      sol: ['A = a · h<sub>a</sub>', `${A} ${e}² = ${a} ${e} · h<sub>a</sub>`, `h<sub>a</sub> = ${A} ${e}² : ${a} ${e}`, `h<sub>a</sub> = ${h} ${e}`] };
  },
  rueckDreieck() {
    const g = R(4, 12), h = R(2, 9), e = pick(['m', 'cm']), A = g * h / 2;
    return { title: 'Rückwärts: Dreieck', q: `Ein dreieckiges Beet hat einen Flächeninhalt von <b>${kz(A)} ${e}²</b> und die Grundseite <b>g = ${g} ${e}</b>. Berechne die <b>Höhe h</b>.`,
      type: 'num', ans: h, pre: 'h =', post: e, hint: 'Erst mal 2 (zwei Dreiecke = Parallelogramm), dann durch g.',
      sol: [`A = ${FR('g · h', '2')}`, `${kz(A)} ${e}² = ${FR(`${g} ${e} · h`, '2')}`, `${kz(2 * A)} ${e}² = ${g} ${e} · h`, `h = ${kz(2 * A)} ${e}² : ${g} ${e}`, `h = ${h} ${e}`] };
  },
  rueckTrapez() {
    const a = R(6, 12), c = R(2, a - 2), h = R(2, 6), e = pick(['m', 'cm']), A = (a + c) * h / 2;
    return { title: 'Rückwärts: Trapez', q: `Ein Trapez hat einen Flächeninhalt von <b>${kz(A)} ${e}²</b>, <b>a = ${a} ${e}</b> und <b>c = ${c} ${e}</b>. Berechne die <b>Höhe h</b>.`,
      type: 'num', ans: h, pre: 'h =', post: e, hint: 'Erst mal 2 (zwei Trapeze = Parallelogramm mit Grundseite a + c), dann durch (a + c).',
      sol: [`A = ${FR('(a + c) · h', '2')}`, `${kz(A)} ${e}² = ${FR(`(${a} ${e} + ${c} ${e}) · h`, '2')}`, `${kz(2 * A)} ${e}² = ${a + c} ${e} · h`, `h = ${kz(2 * A)} ${e}² : ${a + c} ${e}`, `h = ${h} ${e}`] };
  },
  rueckTrapezC() {
    const a = R(6, 12), c = R(2, a - 2), h = pick([2, 4, 5]), e = pick(['m', 'cm']), A = (a + c) * h / 2;
    return { title: 'Rückwärts: Trapez (Seite c)', q: `Ein Trapez hat einen Flächeninhalt von <b>${kz(A)} ${e}²</b>, <b>a = ${a} ${e}</b> und <b>h = ${h} ${e}</b>. Berechne die <b>Seite c</b>.`,
      type: 'num', ans: c, pre: 'c =', post: e, hint: 'Erst mal 2, dann durch h – das ergibt a + c. Dann a abziehen.',
      sol: [`${kz(A)} ${e}² = ${FR(`(${a} ${e} + c) · ${h} ${e}`, '2')}`, `${kz(2 * A)} ${e}² = (${a} ${e} + c) · ${h} ${e}`, `${a} ${e} + c = ${a + c} ${e}`, `c = ${a + c} ${e} − ${a} ${e}`, `c = ${c} ${e}`] };
  },
  /* ===== II.5a Vielecke ===== */
  vieleckA() {
    const art = pick(IM_TEST ? ['L', 'haus'] : ['L', 'haus', 'rt']);   // Test nur ★/★★: das hochkant liegende Trapez (Höhe erst ausrechnen) nur in der Übung
    if (art === 'L') { const a = R(6, 9), b = R(2, 3), c = R(2, 3), d = R(b + 2, b + 4);   // unten a × b, links c × (d − b)
      const A = a * b + c * (d - b);
      return { title: 'Vieleck zerlegen', q: qf('Das L-Beet ist in zwei Rechtecke zerlegt. Berechne den <b>Flächeninhalt</b> des ganzen Beets.',
        figur([[0, 0], [a, 0], [a, b], [c, b], [c, d], [0, d]], { teile: [[[0, 0], [a, 0], [a, b], [0, b]], [[0, b], [c, b], [c, d], [0, d]]], seiten: [[0, 1, `${a} m`], [1, 2, `${b} m`], [3, 4, `${d - b} m`], [4, 5, `${c} m`]] })),
        type: 'num', ans: A, pre: 'A =', post: 'm²', hint: 'Jedes Rechteck einzeln: Länge mal Breite. Dann addieren.',
        sol: [`A₁ = ${a} m · ${b} m = ${a * b} m²`, `A₂ = ${c} m · ${d - b} m = ${c * (d - b)} m²`, `A = ${a * b} m² + ${c * (d - b)} m²`, `A = ${A} m²`] }; }
    if (art === 'haus') { const b = pick([4, 6, 8]), h1 = R(3, 5), h2 = R(2, 4), A = b * h1 + b * h2 / 2;
      return { title: 'Vieleck zerlegen', q: qf('Die Giebelwand besteht aus einem Rechteck und einem Dreieck. Berechne den <b>Flächeninhalt</b> der ganzen Wand.',
        figur([[0, 0], [b, 0], [b, h1], [b / 2, h1 + h2], [0, h1]], { teile: [[[0, 0], [b, 0], [b, h1], [0, h1]], [[0, h1], [b, h1], [b / 2, h1 + h2]]], seiten: [[0, 1, `${b} m`], [1, 2, `${h1} m`]], hoehen: [[[b / 2, h1 + h2], [b / 2, h1], `${h2} m`]] })),
        type: 'num', ans: A, pre: 'A =', post: 'm²', hint: 'Rechteck: Breite mal Höhe. Dreieck: g · h, durch 2. Dann addieren.',
        sol: [`Rechteck: ${b} m · ${h1} m = ${b * h1} m²`, `Dreieck: ${FR(`${b} m · ${h2} m`, '2')} = ${kz(b * h2 / 2)} m²`, `A = ${b * h1} m² + ${kz(b * h2 / 2)} m²`, `A = ${kz(A)} m²`] }; }
    const a = R(5, 8), b = R(3, 5), t = R(2, 4), c = R(1, b - 1);   // Rechteck a × b + rechtwinkliges Trapez rechts (parallel b und c, h = t)
    const A = a * b + (b + c) * t / 2;
    return { title: 'Vieleck zerlegen', q: qf('Das Beet besteht aus einem Rechteck und einem rechtwinkligen Trapez. Berechne den <b>Flächeninhalt</b>.',
      figur([[0, 0], [a + t, 0], [a + t, c], [a, b], [0, b]], { teile: [[[0, 0], [a, 0], [a, b], [0, b]], [[a, 0], [a + t, 0], [a + t, c], [a, b]]], seiten: [[0, 1, `${a + t} m`], [1, 2, `${c} m`], [3, 4, `${a} m`], [4, 0, `${b} m`]] })),
      type: 'num', ans: A, pre: 'A =', post: 'm²', hint: 'Rechteck: a · b. Das Trapez steht hochkant: die parallelen Seiten sind ' + b + ' m und ' + c + ' m, die Höhe ist ' + t + ' m.',
      sol: [`Rechteck: ${a} m · ${b} m = ${a * b} m²`, `Trapez: ${FR(`(${b} m + ${c} m) · ${t} m`, '2')} = ${kz((b + c) * t / 2)} m²`, `A = ${a * b} m² + ${kz((b + c) * t / 2)} m²`, `A = ${kz(A)} m²`] };
  },
  vieleckU() {
    const a = R(6, 9), b = R(2, 3), c = R(2, 3), d = R(b + 2, b + 4), U = 2 * a + 2 * d;
    return { title: 'Umfang eines Vielecks', q: qf('Das L-Beet ist in zwei Rechtecke zerlegt. Berechne den <b>Umfang</b> – nur den Rand ringsum.',
      figur([[0, 0], [a, 0], [a, b], [c, b], [c, d], [0, d]], { teile: [[[0, 0], [a, 0], [a, b], [0, b]], [[0, b], [c, b], [c, d], [0, d]]], seiten: [[0, 1, `${a} m`], [1, 2, `${b} m`], [2, 3, `${a - c} m`], [3, 4, `${d - b} m`], [4, 5, `${c} m`], [5, 0, `${d} m`]] })),
      type: 'num', ans: U, pre: 'U =', post: 'm', hint: 'Nur die Seiten am Rand addieren. Die gestrichelte Zerlegungslinie liegt innen und zählt nicht.',
      sol: [`U = ${a} m + ${b} m + ${a - c} m + ${d - b} m + ${c} m + ${d} m`, `U = ${U} m`] };
  },
  regel() {
    const n = pick([6, 6, 8]), [g, h] = n === 6 ? pick([[4, 3.5], [6, 5.2], [3, 2.6], [10, 8.7]]) : pick([[2, 2.4], [5, 6], [4, 4.8]]), A1 = g * h / 2;
    const R0 = n === 6 ? 1 : 1.307, P = Array.from({ length: n }, (_, i) => [R0 * Math.cos(2 * Math.PI * i / n - Math.PI / 2 - Math.PI / n), R0 * Math.sin(2 * Math.PI * i / n - Math.PI / 2 - Math.PI / n)]);
    const yb = P[0][1];
    return { title: n === 6 ? 'Regelmäßiges Sechseck' : 'Regelmäßiges Achteck', q: qf(`Das regelmäßige ${n === 6 ? 'Sechseck' : 'Achteck'} lässt sich vom Mittelpunkt aus in <b>${n} gleiche Dreiecke</b> zerlegen. Jedes hat <b>g = ${kz(g)} cm</b> und <b>h = ${kz(h)} cm</b>. Berechne den <b>Flächeninhalt</b> des ganzen ${n === 6 ? 'Sechsecks' : 'Achtecks'}.`,
      figur(P.map(p => [p[0] * 4, p[1] * 4]), { seiten: [[0, 1, `g = ${kz(g)} cm`, FB.g]], hoehen: [[[0, 0], [0, yb * 4], `h = ${kz(h)} cm`]], texte: [[0.25, 0.35, 'M', '#1f4e79']] })),
      type: 'num', ans: Math.round(n * A1 * 100) / 100, pre: 'A =', post: 'cm²', hint: 'Ein Dreieck: g · h, durch 2. Dann mal ' + n + '.',
      sol: [`ein Dreieck: ${FR(`${kz(g)} cm · ${kz(h)} cm`, '2')} = ${kz(A1)} cm²`, `A = ${n} · ${kz(A1)} cm²`, `A = ${kz(Math.round(n * A1 * 100) / 100)} cm²`] };
  },
  /* ===== Wiederholung Kapitel I ===== */
  gleichungKlammer() {
    const k = R(2, 5), x = R(2, 9), b = R(1, 6), r = k * (x + b);
    return { title: 'Gleichung mit Klammer', q: `Löse die Gleichung.${big(`${k} · (x + ${b}) = ${r}`)}`, type: 'num', ans: x, pre: 'x =',
      hint: 'Erst die Klammer ausmultiplizieren (oder beide Seiten durch ' + k + ' teilen), dann nach x auflösen.',
      sol: [`${k} · (x + ${b}) = ${r}   | : ${k}`, `x + ${b} = ${x + b}   | − ${b}`, `x = ${x}`] };
  }
};

/* Taschenrechner erlaubt (wie im Terme-Check). */
const MIT_TR = new Set();

/* ---------- Die Aufgabenplätze: 10 zum Thema (seit 27.11. mit „Formel herleiten“) (je einer pro „Ich kann …“-Zeile) + 1 Wiederholung. Test ≈ 20 Minuten.
   Reihenfolge NICHT ändern, solange Ergebnisse aus laufenden Tests eingesammelt werden. CAN wortgleich im Kompetenzraster. */
const SLOTS = [
  { area: 'II.1 Rechteck und Quadrat', name: 'Rechteck und Quadrat', gens: ['rechteckA', 'rechteckU'], back: ['rueckRechteck'] },
  { area: 'II.2a Parallelogramm', name: 'Parallelogramm', gens: ['paraA'], practiceGens: ['paraA', 'paraU'], back: ['rueckPara'] },
  { area: 'II.2b Höhe im Parallelogramm', name: 'Höhe erkennen', gens: ['hoeheMC'] },
  { area: 'II.3a Dreieck', name: 'Dreieck', gens: ['dreieckA'], practiceGens: ['dreieckA', 'dreieckU'], back: ['rueckDreieck'] },
  { area: 'II.3b Höhen im Dreieck', name: 'Seite und ihre Höhe', gens: ['dreieckRecht', 'dreieckSeite'] },
  { area: 'II.4a Trapez', name: 'Trapez', gens: ['trapezA'], practiceGens: ['trapezA', 'trapezU'], back: ['rueckTrapez'], backPractice: ['rueckTrapez', 'rueckTrapezC'] },
  { area: 'II.4a Trapez', name: 'Formel herleiten', gens: ['herleitTrapez'], practiceGens: ['herleitTrapez', 'herleitTrapez', 'herleitDreieck'] },
  { area: 'II.5a Vielecke', name: 'Vielecke zerlegen', gens: ['vieleckA', 'vieleckU'] },
  { area: 'II.5a Vielecke', name: 'Regelmäßige Vielecke', gens: ['regel'] },
  { area: 'Wiederholung: Gleichungen (Kapitel I)', name: 'Gleichung mit Klammer', gens: ['gleichungKlammer'], review: true }
];
/* 27.11.2026 (Malte): Rückwärtsrechnen gehört zu jeder Figur (Unterpunkt im Raster). In der Übung mischen sich vorwärts und rückwärts;
   im Test kommen GENAU ZWEI Figuren rückwärts: eine leichte (Rechteck oder Parallelogramm) und eine schwere (Dreieck oder Trapez). */
const RUECK_LEICHT = [0, 1], RUECK_SCHWER = [3, 5];   // Plätze Rechteck, Parallelogramm | Dreieck, Trapez (seit 27.11. ohne Flächeneinheiten)
SLOTS.forEach(s => { if (s.back) s.practiceGens = [...(s.practiceGens || s.gens), ...(s.backPractice || s.back)]; });
const testArea = s => s.area;
const testKopf = s => `${s.area} · ${s.name}`;
const CAN = [
  'den Umfang und den Flächeninhalt von Rechtecken und Quadraten berechnen – auch rückwärts eine fehlende Seite.',
  'den Flächeninhalt und den Umfang eines Parallelogramms berechnen – mit der Höhe, nicht mit der schrägen Seite – auch rückwärts die Höhe oder die Seite.',
  'die Höhe zu einer Seite erkennen und einzeichnen – auch wenn sie außerhalb liegt.',
  'den Flächeninhalt und den Umfang eines Dreiecks berechnen – auch rückwärts die Höhe oder die Grundseite.',
  'zu jeder Seite die passende Höhe nehmen – auch im rechtwinkligen Dreieck.',
  'den Flächeninhalt und den Umfang eines Trapezes berechnen – auch eines rechtwinkligen – auch rückwärts die Höhe oder die Seite c.',
  'die Formel des Trapezes aus dem Parallelogramm herleiten: warum a + c, warum die Höhe bleibt und warum durch 2 – genauso beim Dreieck.',
  'Vielecke in bekannte Figuren zerlegen und Flächeninhalt und Umfang berechnen.',
  'ein regelmäßiges Sechseck oder Achteck in gleiche Dreiecke zerlegen und den Flächeninhalt berechnen.',
  'Gleichungen mit einer Klammer lösen.'
];
const RASTER = {};
SLOTS.forEach((s, i) => [...new Set([...s.gens, ...(s.practiceGens || [])])].forEach(g => RASTER[g] = CAN[i]));

function makeTask(gen) { const t = G[gen](); t.gen = gen; t.tr = MIT_TR.has(gen); t.can = RASTER[gen]; return t; }

/* Rückmeldung in der Sprache des Kompetenzrasters: nach Abschnitten geordnet, je Aufgabe der „Ich kann …“-Satz */
function rasterReport(tasks, grades, withButtons = false) {
  const sym = g => g === 2 ? '<span class="g2">✓</span>' : g === 1 ? '<span class="g1">½</span>' : '<span class="g0">✗</span>';
  const idx = tasks.map((t, i) => i).sort((a, b) => tasks[a].slot - tasks[b].slot);
  let html = '', area = '';
  for (const i of idx) {
    const t = tasks[i];
    if (SLOTS[t.slot].area !== area) { if (area) html += '</div>'; area = SLOTS[t.slot].area; html += `<div class="rarea${SLOTS[t.slot].review ? ' rev' : ''}"><div class="rhead">${SLOTS[t.slot].review ? `🔁 ${area} <span class="muted" style="font-weight:400">(nicht im Kompetenzraster)</span>` : area}</div>`; }
    html += `<div class="rrow"><span class="sy">${sym(grades[i])}</span><span class="txt">Ich kann ${t.can}</span>${withButtons && grades[i] !== 2 ? ` <button class="mini" data-i="${t.slot}">üben</button>` : ''}</div>`;
  }
  return `<div class="rreport">${html}</div></div>`;
}

/* Übung: echter Zufall. slotIdx = null → alle Plätze; sonst n Aufgaben eines Platzes */
function practiceTasks(slotIdx = null, n = 5) {
  rand = Math.random;
  const gens = s => s.practiceGens || s.gens;   // die Übung darf mehr Varianten haben als der Test
  if (slotIdx === null) return shuffle(SLOTS.map((s, i) => Object.assign(makeTask(pick(gens(s))), { slot: i })));   // Übung gemischt, Test fest
  return Array.from({ length: n }, () => Object.assign(makeTask(pick(gens(SLOTS[slotIdx]))), { slot: slotIdx }));
}

/* Test: Aufgabentyp hängt nur vom Testcode ab (gleich für die ganze Klasse),
   die Zahlen hängen von Testcode + Listennummer ab (jeder bekommt andere). */
/* Bruchgleichungen tauschen (sie kommen erst nach den Ferien dran, die Schüler üben aber schon vorher):
   in der Übung per Knopf, im Test, wenn die Lehrkraft den Test „ohne Bruchgleichungen“ anlegt (steckt im Testcode: 1. Ziffer ungerade).
   Ersatz im Test: eine Gleichung bzw. ein Minus-vor-der-Klammer-Term aus I.5. */
const ERSATZ_TEST = [];
const ohneBruch = code => +String(code)[0] % 2 === 1;
function swapTask() {
  rand = Math.random;
  const i = pick(SLOTS.map((s, k) => k).filter(k => !SLOTS[k].review && !SLOTS[k].tauschbar)), s = SLOTS[i];
  return Object.assign(makeTask(pick(s.practiceGens || s.gens)), { slot: i, getauscht: true });
}
function testTasks(code, nr) {
  IM_TEST = true;
  const out = SLOTS.map((s, i) => {
    rand = mulberry32(hash32(`typ|${code}|${i}`));
    const ers = s.tauschbar && ohneBruch(code) ? pick(ERSATZ_TEST) : null;
    const rl = mulberry32(hash32(`rueck|${code}`)), leicht = RUECK_LEICHT[Math.floor(rl() * 2)], schwer = RUECK_SCHWER[Math.floor(rl() * 2)];
    const gen = ers ? ers.gen : (i === leicht || i === schwer) ? pick(s.back) : pick(s.gens);
    rand = mulberry32(hash32(`zahl|${code}|${nr}|${i}`));
    return Object.assign(makeTask(gen), { slot: ers ? ers.slot : i });
  });
  rand = Math.random; IM_TEST = false;
  return out;
}

/* ---------- Bewerten ----------
   ans: { k } bei Auswahl, sonst { a1 } als Text. Ergebnis: 2 = richtig, 1 = halb (gleichwertig, aber Form nicht ganz fertig), 0 = falsch, -1 = leer */
function grade(t, ans) {
  if (!ans) return -1;
  if (t.type === 'mc') return ans.k == null ? -1 : (t.options[ans.k] === t.ans ? 2 : 0);
  if (t.type === 'term') return gradeTerm(t, ans.a1 || '');
  const v1 = parseNum(ans.a1 || '');
  if (t.type === 'num') return isNaN(v1) ? (String(ans.a1 || '').trim() ? 0 : -1) : (eq(v1, t.ans) ? 2 : 0);
  return 0;
}
/* Was bei ½ fehlt – für die Rückmeldung in der Übung */
const HALF_TIP = {
  sum: 'Der Term stimmt, ist aber noch nicht fertig: Löse alle Klammern auf und fasse gleiche Glieder zusammen.',
  factor: 'Richtig umgeformt – aber in der Klammer steckt noch ein gemeinsamer Faktor. Klammere so viel wie möglich aus.',
  binomK: 'Gleichwertig – aber noch nicht fertig: Erst die gemeinsame Zahl ausklammern, dann den Rest in der Klammer mit einer binomischen Formel faktorisieren, z. B. 2 · (x + 3) · (x − 3).',
  binom: 'Gleichwertig – aber noch nicht als binomische Klammer geschrieben. Schreibe das Ergebnis als (… + …)², (… − …)² oder (… + …) · (… − …).'
};
const points = g => g === 2 ? 1 : g === 1 ? 0.5 : 0;
const fmtPts = p => String(p).replace('.', ',');
/* Note linear (Realschule): volle Punktzahl = 1,0, halbe Punktzahl = 3,5, null Punkte = 6,0; auf eine Dezimale gerundet */
const noteFor = (pts, max = SLOTS.length) => Math.round((6 - 5 * pts / max) * 10 + 1e-9) / 10;
const fmtNote = n => n.toFixed(1).replace('.', ',');

/* Antwort lesbar machen (für Lehrerseite und Ergebnisanzeige) */
function answerText(t, ans) {
  if (!ans) return '—';
  if (t.type === 'mc') return ans.k == null ? '—' : t.options[ans.k];
  const a1 = String(ans.a1 || '').trim();
  if (!a1) return '—';
  if (t.type === 'term') return termHtml(a1);
  return `${t.pre ? t.pre + ' ' : ''}${escH(a1)}${t.post ? ' ' + t.post : ''}`;
}
function correctText(t) {
  if (t.type === 'mc') return t.ans;
  if (t.type === 'term') return t.ansHtml;
  if (t.type === 'num') return `${t.pre ? t.pre + ' ' : ''}${t.post === '€' ? t.ans.toFixed(2).replace('.', ',') : fmt(t.ans)}${t.post ? ' ' + t.post : ''}`;
}

/* ---------- Testcode: 4 Zufallsziffern + 1 Prüfziffer (fängt Tippfehler ab) ---------- */
function codeCheckDigit(d4) { const w = [3, 7, 9, 1]; return String([...d4].reduce((s, c, i) => s + (+c) * w[i], 0) % 10); }
function newTestCode(ohneBr = false) { let d; do { d = String(Math.floor(Math.random() * 10000)).padStart(4, '0'); } while ((+d[0] % 2 === 1) !== ohneBr); return d + codeCheckDigit(d); }
function validCode(c) { return /^\d{5}$/.test(c) && codeCheckDigit(c.slice(0, 4)) === c[4]; }

/* ---------- Schülernummer: 3 Ziffern, die letzte ist Prüfziffer ----------
   Gültig, wenn (3·d1 + 7·d2 + d3) mod 10 = 0. Das ergibt 90 mögliche Nummern (genug für eine Klasse)
   und fängt Zahlendreher und einzelne Tippfehler ab. Die Nummer verrät nichts über die Klassenliste. */
function validNr(n) {
  const s = String(n).trim();
  if (!/^[1-9]\d\d$/.test(s)) return false;
  return (3 * +s[0] + 7 * +s[1] + +s[2]) % 10 === 0;
}
const ALL_NRS = Array.from({ length: 900 }, (_, i) => i + 100).filter(validNr);
function randomNrs(count) {
  const pool = ALL_NRS.slice();
  for (let i = pool.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [pool[i], pool[j]] = [pool[j], pool[i]]; }
  return pool.slice(0, Math.min(count, pool.length)).sort((a, b) => a - b);
}

/* ---------- Übungsstatistik (bleibt auf dem Schülergerät, bis sie per QR gezeigt wird) ----------
   { dev, rounds, drills, tasks, correct, days: ['2026-10-18', …], minutes, last } */
const today = () => { const d = new Date(); return `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}-${String(d.getDate()).padStart(2, '0')}`; };
function encPractice(p) {
  if (!p) return '';
  return [p.dev, p.rounds, p.drills, p.tasks, p.correct, p.days.length, Math.round(p.minutes), (p.last || '').replace(/-/g, '')].join('.');
}
function decPractice(s) {
  if (!s) return null;
  const [dev, rounds, drills, tasks, correct, days, minutes, last] = s.split('.');
  return { dev, rounds: +rounds, drills: +drills, tasks: +tasks, correct: +correct, days: +days, minutes: +minutes,
    last: last ? `${last.slice(0, 4)}-${last.slice(4, 6)}-${last.slice(6, 8)}` : '' };
}

/* ---------- Ergebnis-Übertragung per QR-Code ----------
   Test:  TC1|code|nr|tabs|minuten|antworten|übung|prüfsumme  (die Lehrerseite bewertet anhand der Antworten selbst neu)
   Übung: TU1|nr|übung|prüfsumme                               (Übungsnachweis, auch von einem anderen Gerät) */
const SALT = 'Hoeri-Flaechen';
/* Stand der Aufgaben: bei jeder Änderung an Generatoren/SLOTS erhöhen (und ?v= in index.html/lehrer.html anpassen).
   Steckt im Ergebnis-Code, damit die Lehrerseite merkt, wenn ein Schülergerät eine andere Fassung hatte. */
const APPV = '20261127e';
const sig = s => hash32(SALT + '|' + s).toString(36).toUpperCase().padStart(7, '0').slice(-5);
function encAnswers(answers) {
  return answers.map(a => !a ? '' : a.k != null ? '#' + a.k : [a.a1 || '', a.a2 || ''].map(x => encodeURIComponent(String(x).trim()).replace(/!/g, '%21').replace(/~/g, '%7E')).join('~')).join('!');
}
function decAnswers(s) {
  return s.split('!').map(x => {
    if (x === '') return null;
    if (x[0] === '#') return { k: +x.slice(1) };
    const [a1, a2] = x.split('~').map(decodeURIComponent);
    return { a1, a2 };
  });
}
function makePayload(code, nr, tabs, minutes, answers, practice) {
  const body = ['TC1.' + APPV, code, nr, tabs, minutes, encAnswers(answers), encPractice(practice)].join('|');
  return body + '|' + sig(body);
}
function makePracticePayload(nr, practice) {
  const body = ['TU1', nr, encPractice(practice)].join('|');
  return body + '|' + sig(body);
}
function parsePayload(txt) {
  const p = String(txt).trim().split('|');
  if (/^TC1(\.|$)/.test(p[0]) && p.length === 8) {
    const body = p.slice(0, 7).join('|');
    return { kind: 'test', version: p[0].split('.')[1] || '', code: p[1], nr: +p[2], tabs: +p[3], minutes: +p[4], answers: decAnswers(p[5]), practice: decPractice(p[6]), valid: sig(body) === p[7] };
  }
  if (p[0] === 'TU1' && p.length === 4) {
    const body = p.slice(0, 3).join('|');
    return { kind: 'practice', nr: +p[1], practice: decPractice(p[2]), valid: sig(body) === p[3] };
  }
  return null;
}
/* Kurzcode zum Abtippen (ohne Antworten und Übung): Nr-Bewertungen-Tabwechsel-Prüfsumme, z. B. 417-222120222202-0-K3F9A */
function makeShortCode(code, nr, tabs, grades) {
  const g = grades.map(x => Math.max(0, x)).join('');
  return `${nr}-${g}-${tabs}-${sig(`S|${code}|${nr}|${g}|${tabs}`)}`;
}
function parseShortCode(txt, code) {
  const m = String(txt).trim().toUpperCase().replace(/\s/g, '').match(new RegExp(`^(\\d{3})-([012]{${SLOTS.length}})-(\\d{1,3})-([0-9A-Z]{5})$`));
  if (!m) return null;
  const [, nr, g, tabs, s] = m;
  return { nr: +nr, grades: [...g].map(Number), tabs: +tabs, valid: sig(`S|${code}|${+nr}|${g}|${+tabs}`) === s };
}
