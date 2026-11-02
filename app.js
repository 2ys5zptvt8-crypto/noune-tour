'use strict';
/* Sentiers — boucles de randonnée autour de soi, carte hors ligne, enregistrement GPS.
   Tout est stocké sur le téléphone (localStorage + Cache API). */

const ORS_URL = 'https://api.openrouteservice.org/v2/directions/foot-hiking/geojson';
const TILE_URL = 'https://data.geopf.fr/wmts?SERVICE=WMTS&REQUEST=GetTile&VERSION=1.0.0&LAYER=GEOGRAPHICALGRIDSYSTEMS.PLANIGNV2&STYLE=normal&FORMAT=image/png&TILEMATRIXSET=PM&TILEMATRIX={z}&TILEROW={y}&TILECOL={x}';
const TILE_CACHE = 'sentiers-tiles-v1';
const OFFLINE_ZOOMS = { bbox: [11, 12, 13, 14], corridor: [15, 16] };
const MAX_TILES = 2500;
const COLORS = ['#d9480f', '#1971c2', '#7048e8', '#2b8a3e', '#c2255c', '#e67700'];
const TRAIL_TYPES = new Set([4, 5, 7, 8]); // ORS waytype : sentier, chemin, piéton, escaliers
const DIRS = ['Nord', 'Nord-Est', 'Est', 'Sud-Est', 'Sud', 'Sud-Ouest', 'Ouest', 'Nord-Ouest'];

/* ---------- Stockage ---------- */
const store = {
  get(k, d) { try { const v = localStorage.getItem('sentiers.' + k); return v == null ? d : JSON.parse(v); } catch (e) { return d; } },
  set(k, v) { try { localStorage.setItem('sentiers.' + k, JSON.stringify(v)); return true; } catch (e) { toast('Mémoire pleine : supprime d\'anciennes randos'); return false; } },
  del(k) { try { localStorage.removeItem('sentiers.' + k); } catch (e) {} }
};

const state = {
  settings: Object.assign({ key: '', pace: 4.5 }, store.get('settings', {})),
  routes: store.get('routes', []),
  history: store.get('history', []),
  pos: null, custom: null, results: [], selected: -1,
  hike: null, watchId: null, timer: null, wake: null, follow: true, tab: 'explore'
};

/* ---------- Utilitaires ---------- */
const $ = (s) => document.querySelector(s);
const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const uid = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 6);
const km = (m, d = 1) => (m / 1000).toFixed(d).replace('.', ',');
function fmtDur(min) { min = Math.round(min); const h = Math.floor(min / 60), m = min % 60; return h ? `${h} h ${String(m).padStart(2, '0')}` : `${m} min`; }
function fmtClock(ms) { const s = Math.floor(ms / 1000); return `${Math.floor(s / 3600)}:${String(Math.floor(s / 60) % 60).padStart(2, '0')}:${String(s % 60).padStart(2, '0')}`; }
function fmtDate(t) { return new Date(t).toLocaleDateString('fr-FR', { weekday: 'short', day: 'numeric', month: 'short' }); }
function hav(a, b) {
  const R = 6371000, r = Math.PI / 180, dLa = (b[0] - a[0]) * r, dLo = (b[1] - a[1]) * r;
  const x = Math.sin(dLa / 2) ** 2 + Math.cos(a[0] * r) * Math.cos(b[0] * r) * Math.sin(dLo / 2) ** 2;
  return 2 * R * Math.asin(Math.sqrt(x));
}
function cumDist(ll) { const c = [0]; for (let i = 1; i < ll.length; i++) c.push(c[i - 1] + hav(ll[i - 1], ll[i])); return c; }
function median(a) { const s = [...a].sort((x, y) => x - y); return s[Math.floor(s.length / 2)]; }
let toastT;
function toast(msg, ms = 2800) { const t = $('#toast'); t.textContent = msg; t.classList.add('show'); clearTimeout(toastT); toastT = setTimeout(() => t.classList.remove('show'), ms); }
function banner(msg, kind) { const b = $('#banner'); if (!msg) { b.hidden = true; return; } b.textContent = msg; b.className = kind || ''; b.hidden = false; }
function estimateMin(dist, ascent) { return (dist / 1000) / state.settings.pace * 60 + (ascent || 0) / 400 * 60; }
function difficulty(dist, ascent) { const e = dist / 1000 + (ascent || 0) / 100; return e < 10 ? 'Facile' : e < 18 ? 'Moyenne' : 'Difficile'; }
function direction(start, ll) {
  let la = 0, lo = 0; ll.forEach((p) => { la += p[0]; lo += p[1]; }); la /= ll.length; lo /= ll.length;
  const ang = Math.atan2((lo - start[1]) * Math.cos(start[0] * Math.PI / 180), la - start[0]) * 180 / Math.PI;
  return DIRS[Math.round(((ang + 360) % 360) / 45) % 8];
}
function ascentOf(ele) {
  let up = 0, ref = null;
  for (const e of ele) { if (e == null) continue; if (ref == null) ref = e; else if (e - ref > 2) { up += e - ref; ref = e; } else if (ref - e > 2) ref = e; }
  return Math.round(up);
}

/* ---------- Carte ---------- */
const view0 = store.get('view', { c: [46.6, 2.4], z: 6 });
const map = L.map('map', { zoomControl: false, attributionControl: true, tap: true }).setView(view0.c, view0.z);
let tiles = makeTiles(false);
function makeTiles(offline) {
  return L.tileLayer(TILE_URL, {
    maxZoom: 18, maxNativeZoom: offline ? 16 : 18, minZoom: 5,
    attribution: '© IGN · © OpenStreetMap', crossOrigin: false
  }).addTo(map);
}
function setOfflineTiles(on) { map.removeLayer(tiles); tiles = makeTiles(on); }
map.attributionControl.setPrefix(false);
const layers = { results: L.layerGroup().addTo(map), route: L.layerGroup().addTo(map), track: L.layerGroup().addTo(map) };
const startIcon = L.divIcon({ className: '', html: '<div class="start-pin"></div>', iconSize: [22, 22], iconAnchor: [11, 11] });
let startMarker = null, posDot = null, posAcc = null;
map.on('moveend', () => store.set('view', { c: [map.getCenter().lat, map.getCenter().lng], z: map.getZoom() }));
map.on('dragstart', () => { if (state.hike) { state.follow = false; $('#locate').classList.remove('follow'); } });

function showPos(lat, lng, acc) {
  if (!posDot) {
    posAcc = L.circle([lat, lng], { radius: acc, color: '#1971c2', weight: 1, fillOpacity: 0.1, interactive: false }).addTo(map);
    posDot = L.circleMarker([lat, lng], { radius: 8, color: '#fff', weight: 3, fillColor: '#1971c2', fillOpacity: 1, interactive: false }).addTo(map);
  } else { posDot.setLatLng([lat, lng]); posAcc.setLatLng([lat, lng]).setRadius(acc); }
}
function startPoint() { return state.custom || state.pos; }
function updateStart() {
  const s = startPoint();
  $('#startInfo').innerHTML = state.custom ? 'Départ : point choisi sur la carte · <a href="#" id="resetStart">revenir à ma position</a>'
    : (state.pos ? 'Départ : ta position GPS' : 'Départ : ta position GPS (en attente…)');
  const r = $('#resetStart'); if (r) r.onclick = (e) => { e.preventDefault(); state.custom = null; updateStart(); if (state.pos) map.panTo(state.pos); };
  if (s) { if (!startMarker) startMarker = L.marker(s, { icon: startIcon, interactive: false }).addTo(map); else startMarker.setLatLng(s); }
}
map.on('click', (e) => {
  if (state.hike || state.tab !== 'explore') return;
  state.custom = [e.latlng.lat, e.latlng.lng]; updateStart(); clearResults(); toast('Nouveau point de départ');
});

/* ---------- GPS ---------- */
function geoErr(e) {
  if (e.code === 1) return 'Autorise la localisation : Réglages iPhone → Confidentialité → Service de localisation';
  if (e.code === 3) return 'Le GPS met du temps à répondre, réessaie dehors';
  return 'Position introuvable pour le moment';
}
function locate(center) {
  return new Promise((res) => {
    if (!navigator.geolocation) { toast('GPS indisponible sur cet appareil'); return res(null); }
    navigator.geolocation.getCurrentPosition((p) => {
      state.pos = [p.coords.latitude, p.coords.longitude]; showPos(...state.pos, p.coords.accuracy); updateStart();
      if (center) map.setView(state.pos, Math.max(map.getZoom(), 14)); res(state.pos);
    }, (e) => { toast(geoErr(e), 4500); res(null); }, { enableHighAccuracy: true, timeout: 15000, maximumAge: 20000 });
  });
}
$('#locate').onclick = () => {
  if (state.hike) { state.follow = true; $('#locate').classList.add('follow'); if (state.hikePos) map.setView(state.hikePos, Math.max(map.getZoom(), 15)); return; }
  locate(true);
};

/* ---------- Onglets & panneau ---------- */
function setTab(t) {
  state.tab = t;
  document.querySelectorAll('#tabs button').forEach((b) => b.classList.toggle('active', b.dataset.tab === t));
  document.querySelectorAll('.view').forEach((v) => { v.hidden = v.dataset.view !== t; });
  $('.sheet-body').scrollTop = 0;
  layers.track.clearLayers();
  if (t !== 'explore') layers.results.clearLayers(); else drawResults();
  if (t !== 'routes') layers.route.clearLayers();
  if (t === 'routes') renderRoutes();
  if (t === 'history') renderHistory();
  if (t === 'settings') renderSettings();
  if (t === 'explore') updateStart();
  setSheet(t === 'explore' && !state.results.length ? 'mid' : 'mid');
}
document.querySelectorAll('#tabs button').forEach((b) => (b.onclick = () => setTab(b.dataset.tab)));
let sheetMode = 'mid';
function setSheet(m) {
  sheetMode = m;
  const h = m === 'low' ? '150px' : m === 'high' ? '78dvh' : (state.hike ? '370px' : '46dvh');
  document.documentElement.style.setProperty('--sheet-h', h);
  setTimeout(() => map.invalidateSize(), 280);
}
$('#handle').onclick = () => setSheet(sheetMode === 'mid' ? 'high' : sheetMode === 'high' ? 'low' : 'mid');

/* ---------- Recherche de boucles ---------- */
const distInput = $('#dist');
function syncDist() {
  $('#distVal').textContent = String(+distInput.value).replace('.', ',');
  document.querySelectorAll('#presets button').forEach((b) => b.classList.toggle('on', +b.dataset.km === +distInput.value));
  store.set('lastKm', +distInput.value);
}
distInput.value = store.get('lastKm', 8); syncDist();
distInput.oninput = syncDist;
document.querySelectorAll('#presets button').forEach((b) => (b.onclick = () => { distInput.value = b.dataset.km; syncDist(); }));

async function orsLoop(start, length, seed, points) {
  const r = await fetch(ORS_URL, {
    method: 'POST',
    headers: { Authorization: state.settings.key, 'Content-Type': 'application/json', Accept: 'application/geo+json, application/json' },
    body: JSON.stringify({
      coordinates: [[start[1], start[0]]], elevation: true, instructions: false, preference: 'recommended',
      extra_info: ['waytype'], options: { round_trip: { length: Math.round(length), points, seed } }
    })
  });
  if (!r.ok) {
    let msg = ''; try { const j = await r.json(); msg = (j.error && (j.error.message || j.error)) || j.message || ''; } catch (e) {}
    const err = new Error(typeof msg === 'string' ? msg : 'HTTP ' + r.status); err.status = r.status;
    err.fatal = r.status === 401 || r.status === 403 || r.status === 429; throw err;
  }
  const j = await r.json(); const f = j.features && j.features[0];
  if (!f) throw new Error('Réponse vide');
  return parseRoute(f, start);
}
function parseRoute(f, start) {
  const c = f.geometry.coordinates, s = (f.properties && f.properties.summary) || {};
  const latlngs = c.map((p) => [+p[1].toFixed(6), +p[0].toFixed(6)]);
  const ele = c.map((p) => (p.length > 2 && p[2] != null ? Math.round(p[2]) : null));
  const wt = (f.properties.extras && f.properties.extras.waytype && f.properties.extras.waytype.summary) || [];
  let trail = 0; wt.forEach((w) => { if (TRAIL_TYPES.has(w.value)) trail += w.amount || 0; });
  const distance = s.distance || cumDist(latlngs).at(-1);
  const ascent = s.ascent != null ? Math.round(s.ascent) : ascentOf(ele);
  return { latlngs, ele, distance, ascent, trail: Math.round(trail), start, name: 'Boucle ' + direction(start, latlngs) };
}
function similar(a, b) {
  if (Math.abs(a.distance - b.distance) / a.distance > 0.06) return false;
  const pick = (r) => [0.25, 0.5, 0.75].map((f) => r.latlngs[Math.floor(f * (r.latlngs.length - 1))]);
  const pa = pick(a), pb = pick(b);
  return pa.every((p, i) => hav(p, pb[i]) < 250);
}
let searching = false;
async function findLoops() {
  if (searching) return;
  if (!state.settings.key) { setTab('settings'); toast('Ajoute d\'abord ta clé gratuite openrouteservice', 4000); return; }
  if (!navigator.onLine) { toast('Pas de réseau : les boucles se calculent avec Internet. Tes boucles gardées marchent hors ligne.', 4500); return; }
  let start = startPoint();
  const btn = $('#search'), box = $('#results');
  searching = true; btn.disabled = true; btn.textContent = 'Recherche en cours…';
  clearResults(); box.innerHTML = '<div class="loading"><span class="spin"></span>Je cherche des sentiers autour de toi…</div>';
  try {
    if (!start) start = await locate(true);
    if (!start) { box.innerHTML = '<div class="err">Je n\'ai pas ta position. Autorise la localisation ou touche la carte pour choisir un départ.</div>'; return; }
    const target = +distInput.value * 1000, base = Math.floor(Math.random() * 1000);
    let factor = store.get('orsFactor', 0.85); const found = []; let lastErr = null, done = 0;
    for (let b = 0; b < 3 && found.length < 5; b++) {
      const batch = [0, 1, 2].map((i) => ({ seed: base + b * 3 + i, points: (b + i) % 2 ? 4 : 5 }));
      const res = await Promise.all(batch.map((a) => orsLoop(start, target * factor, a.seed, a.points).catch((e) => ({ error: e }))));
      const ratios = [];
      for (const r of res) {
        if (r.error) { lastErr = r.error; if (r.error.fatal) throw r.error; continue; }
        done++; ratios.push(r.distance / (target * factor));
        const off = Math.abs(r.distance - target) / target;
        if (off <= 0.3 && !found.some((f) => similar(f, r))) found.push(r);
      }
      if (ratios.length) { factor = Math.min(1.4, Math.max(0.5, 1 / median(ratios))); store.set('orsFactor', factor); }
      box.innerHTML = `<div class="loading"><span class="spin"></span>${found.length} boucle${found.length > 1 ? 's' : ''} trouvée${found.length > 1 ? 's' : ''}…</div>`;
    }
    if (!found.length) {
      box.innerHTML = `<div class="err">${done ? 'Pas de boucle proche de cette distance ici. Essaie une autre distance ou déplace le départ.' : 'Le calcul a échoué' + (lastErr ? ' : ' + esc(lastErr.message) : '') + '.'}</div>`;
      return;
    }
    found.forEach((r) => { r.score = r.trail / 100 - Math.abs(r.distance - target) / target * 1.5; });
    found.sort((a, b) => b.score - a.score);
    state.results = found.slice(0, 4).map((r, i) => Object.assign(r, { color: COLORS[i] }));
    state.selected = -1; renderResults(); drawResults(true); setSheet('mid');
  } catch (e) {
    const msg = e.status === 401 || e.status === 403 ? 'Clé refusée. Vérifie-la dans Réglages.'
      : e.status === 429 ? 'Limite gratuite atteinte pour aujourd\'hui. Réessaie plus tard.'
      : 'Impossible de joindre le service de calcul. Vérifie ta connexion.';
    box.innerHTML = `<div class="err">${msg}</div>`;
  } finally { searching = false; btn.disabled = false; btn.textContent = state.results.length ? 'Proposer d\'autres boucles' : 'Proposer des boucles'; }
}
$('#search').onclick = findLoops;

function clearResults() { state.results = []; state.selected = -1; layers.results.clearLayers(); $('#results').innerHTML = ''; $('#search').textContent = 'Proposer des boucles'; }

function sparkline(ele, latlngs, color) {
  const pts = ele.map((e, i) => [i, e]).filter((p) => p[1] != null);
  if (pts.length < 2) return '';
  const cd = cumDist(latlngs), total = cd.at(-1) || 1;
  const vals = pts.map((p) => p[1]); const lo = Math.min(...vals), hi = Math.max(...vals), span = Math.max(hi - lo, 20);
  const step = Math.max(1, Math.floor(pts.length / 120));
  let d = ''; for (let k = 0; k < pts.length; k += step) { const [i, e] = pts[k]; d += (d ? 'L' : 'M') + (cd[i] / total * 300).toFixed(1) + ',' + (40 - (e - lo) / span * 34).toFixed(1); }
  return `<svg class="spark" viewBox="0 0 300 44" preserveAspectRatio="none"><path d="${d}L300,44L0,44Z" fill="${color}" opacity=".14"/><path d="${d}" fill="none" stroke="${color}" stroke-width="2" vector-effect="non-scaling-stroke"/><text x="2" y="10" font-size="10" fill="currentColor" opacity=".6">${hi} m</text><text x="2" y="42" font-size="10" fill="currentColor" opacity=".6">${lo} m</text></svg>`;
}
function routeCardHTML(r, color, extra) {
  const diff = difficulty(r.distance, r.ascent);
  return `<div class="rtop"><span class="rname">${esc(r.name)}</span><span class="badge b-${diff.toLowerCase()}">${diff}</span></div>
    <div class="rmeta">${km(r.distance)} km · ↗ ${r.ascent} m · ≈ ${fmtDur(estimateMin(r.distance, r.ascent))}</div>
    <div class="trail"><span>Sentiers</span><span class="bar"><i style="width:${r.trail}%"></i></span><span>${r.trail} %</span></div>
    ${sparkline(r.ele || [], r.latlngs, color)}${extra || ''}`;
}
function renderResults() {
  const box = $('#results');
  box.innerHTML = '<p class="muted" style="margin-top:14px">Touche une boucle pour la voir sur la carte.</p>';
  state.results.forEach((r, i) => {
    const el = document.createElement('div');
    el.className = 'rcard' + (state.selected === i ? ' sel' : ''); el.style.setProperty('--c', r.color);
    el.innerHTML = routeCardHTML(r, r.color, `<div class="ractions"><button class="primary" data-act="keep">Garder pour hors ligne</button></div><div class="progress" hidden><i></i></div>`);
    el.onclick = (e) => { if (e.target.closest('button')) return; selectResult(i); };
    el.querySelector('[data-act=keep]').onclick = (e) => keepRoute(r, el, e.currentTarget);
    box.appendChild(el);
  });
}
function drawResults(fit) {
  layers.results.clearLayers();
  if (!state.results.length) return;
  const all = [];
  state.results.forEach((r, i) => {
    const sel = state.selected === i, dim = state.selected >= 0 && !sel;
    const line = L.polyline(r.latlngs, { color: r.color, weight: sel ? 6 : 4, opacity: dim ? 0.25 : 0.9 }).addTo(layers.results);
    line.on('click', (e) => { L.DomEvent.stop(e); selectResult(i); });
    if (sel) line.bringToFront();
    all.push(...r.latlngs);
  });
  if (fit) map.fitBounds(L.latLngBounds(all), { padding: [30, 30] });
}
function selectResult(i) {
  state.selected = state.selected === i ? -1 : i;
  document.querySelectorAll('#results .rcard').forEach((c, k) => c.classList.toggle('sel', k === state.selected));
  drawResults(false);
  if (state.selected >= 0) map.fitBounds(L.latLngBounds(state.results[i].latlngs), { padding: [30, 30] });
}

/* ---------- Boucles gardées & tuiles hors ligne ---------- */
function tileUrl(z, x, y) { return TILE_URL.replace('{z}', z).replace('{x}', x).replace('{y}', y); }
function lon2x(lon, z) { return Math.floor((lon + 180) / 360 * 2 ** z); }
function lat2y(lat, z) { const r = lat * Math.PI / 180; return Math.floor((1 - Math.log(Math.tan(r) + 1 / Math.cos(r)) / Math.PI) / 2 * 2 ** z); }
function tilesFor(latlngs) {
  const set = new Set();
  let s = 90, n = -90, w = 180, e = -180;
  latlngs.forEach(([la, lo]) => { s = Math.min(s, la); n = Math.max(n, la); w = Math.min(w, lo); e = Math.max(e, lo); });
  for (const z of OFFLINE_ZOOMS.bbox) {
    for (let x = lon2x(w, z) - 1; x <= lon2x(e, z) + 1; x++) for (let y = lat2y(n, z) - 1; y <= lat2y(s, z) + 1; y++) set.add(`${z}/${x}/${y}`);
  }
  // points tous les ~60 m pour ne rater aucune tuile le long du tracé
  const dense = [];
  for (let i = 0; i < latlngs.length; i++) {
    dense.push(latlngs[i]);
    if (i + 1 < latlngs.length) { const d = hav(latlngs[i], latlngs[i + 1]), k = Math.floor(d / 60);
      for (let j = 1; j <= k; j++) dense.push([latlngs[i][0] + (latlngs[i + 1][0] - latlngs[i][0]) * j / (k + 1), latlngs[i][1] + (latlngs[i + 1][1] - latlngs[i][1]) * j / (k + 1)]); }
  }
  for (const z of OFFLINE_ZOOMS.corridor) {
    for (const [la, lo] of dense) { const x = lon2x(lo, z), y = lat2y(la, z); for (let dx = -1; dx <= 1; dx++) for (let dy = -1; dy <= 1; dy++) set.add(`${z}/${x + dx}/${y + dy}`); }
  }
  return [...set];
}
async function downloadTiles(list, onProgress) {
  if (!('caches' in window)) throw new Error('Stockage hors ligne indisponible');
  const cache = await caches.open(TILE_CACHE); const q = list.slice(); let done = 0, fail = 0;
  async function worker() {
    while (q.length) {
      const [z, x, y] = q.shift().split('/'); const url = tileUrl(z, x, y);
      try {
        if (!(await cache.match(url))) {
          let r; try { r = await fetch(url, { mode: 'cors' }); } catch (e) { r = await fetch(url, { mode: 'no-cors' }); }
          if (r.ok || r.type === 'opaque') await cache.put(url, r); else fail++;
        }
      } catch (e) { fail++; }
      onProgress(++done, list.length);
    }
  }
  await Promise.all(Array.from({ length: 6 }, worker));
  return { count: list.length, fail };
}
async function keepRoute(r, card, btn) {
  if (r.savedId) { setTab('routes'); return; }
  if (navigator.storage && navigator.storage.persist) navigator.storage.persist().catch(() => {});
  const route = { id: uid(), name: r.name, createdAt: Date.now(), latlngs: r.latlngs, ele: r.ele, distance: r.distance, ascent: r.ascent, trail: r.trail, start: r.start, offline: false, tiles: 0 };
  state.routes.unshift(route);
  if (!store.set('routes', state.routes)) { state.routes.shift(); return; }
  r.savedId = route.id;
  btn.disabled = true; btn.textContent = 'Téléchargement de la carte…';
  const bar = card.querySelector('.progress'); bar.hidden = false;
  await fetchRouteTiles(route, (d, t) => { bar.firstChild.style.width = (d / t * 100) + '%'; });
  bar.hidden = true; btn.disabled = false;
  btn.textContent = route.offline ? '✓ Gardée · voir Mes boucles' : 'Gardée · carte incomplète';
  toast(route.offline ? 'Boucle prête pour marcher sans réseau' : 'Boucle gardée, mais la carte n\'a pas pu être téléchargée en entier');
}
async function fetchRouteTiles(route, onProgress) {
  const list = tilesFor(route.latlngs).slice(0, MAX_TILES);
  try {
    const { count, fail } = await downloadTiles(list, onProgress);
    route.offline = fail / count < 0.05; route.tiles = count;
  } catch (e) { route.offline = false; }
  store.set('routes', state.routes);
}

function renderRoutes() {
  const box = $('#routesList'); box.innerHTML = '';
  if (!state.routes.length) { box.innerHTML = '<div class="empty">Aucune boucle gardée pour l\'instant.<br>Dans Explorer, choisis une boucle et touche « Garder pour hors ligne ».</div>'; return; }
  state.routes.forEach((r, i) => {
    const color = COLORS[i % COLORS.length], el = document.createElement('div');
    el.className = 'rcard'; el.style.setProperty('--c', color);
    const status = r.offline ? '<span class="offline-ok">✓ Carte disponible hors ligne</span>' : '<span class="offline-no">Carte pas encore téléchargée</span>';
    el.innerHTML = routeCardHTML(r, color, `${status}<div class="ractions">
      <button class="primary" data-act="go">Démarrer</button>
      ${r.offline ? '' : '<button class="secondary" data-act="dl">Télécharger</button>'}
      <button class="ghost" data-act="del" aria-label="Supprimer">🗑</button></div><div class="progress" hidden><i></i></div>`);
    el.onclick = (e) => { if (e.target.closest('button')) return; showRoute(r, color); };
    el.querySelector('[data-act=go]').onclick = () => startHike(r);
    el.querySelector('[data-act=del]').onclick = () => {
      if (!confirm(`Supprimer « ${r.name} » ?`)) return;
      state.routes = state.routes.filter((x) => x.id !== r.id); store.set('routes', state.routes); layers.route.clearLayers(); renderRoutes();
    };
    const dl = el.querySelector('[data-act=dl]');
    if (dl) dl.onclick = async () => {
      if (!navigator.onLine) { toast('Il faut du réseau pour télécharger la carte'); return; }
      dl.disabled = true; dl.textContent = '…'; const bar = el.querySelector('.progress'); bar.hidden = false;
      await fetchRouteTiles(r, (d, t) => { bar.firstChild.style.width = (d / t * 100) + '%'; }); renderRoutes();
    };
    box.appendChild(el);
  });
}
function showRoute(r, color) {
  layers.route.clearLayers();
  L.polyline(r.latlngs, { color: color || '#d9480f', weight: 5 }).addTo(layers.route);
  L.marker(r.latlngs[0], { icon: startIcon, interactive: false }).addTo(layers.route);
  map.fitBounds(L.latLngBounds(r.latlngs), { padding: [30, 30] });
}
$('#freeHike').onclick = () => startHike(null);

/* ---------- Rando en cours ---------- */
async function requestWake() {
  try { if ('wakeLock' in navigator && !state.wake) { state.wake = await navigator.wakeLock.request('screen'); state.wake.addEventListener('release', () => { state.wake = null; }); $('#wakeHint').textContent = 'Écran maintenu allumé pendant la rando.'; } }
  catch (e) { $('#wakeHint').textContent = 'Garde l\'écran allumé pour que le GPS continue d\'enregistrer.'; }
}
function releaseWake() { try { state.wake && state.wake.release(); } catch (e) {} state.wake = null; }
document.addEventListener('visibilitychange', () => {
  if (document.visibilityState === 'visible' && state.hike && state.hike.running) requestWake();
  if (document.visibilityState === 'hidden') saveActive();
});
window.addEventListener('pagehide', () => saveActive());

function startHike(route, resume) {
  if (state.hike && !resume) return;
  if (!resume) {
    state.hike = { id: uid(), routeId: route ? route.id : null, name: route ? route.name : 'Rando libre', startedAt: Date.now(),
      elapsed: 0, running: true, resumedAt: Date.now(), pts: [], distance: 0, ascent: 0, refAlt: null, idx: 0 };
    store.set('activeHike', state.hike);
  }
  const h = state.hike;
  h.route = h.routeId ? state.routes.find((r) => r.id === h.routeId) : null;
  if (h.route) h.cum = cumDist(h.route.latlngs);
  document.body.classList.add('hiking');
  document.querySelectorAll('.view').forEach((v) => { v.hidden = v.dataset.view !== 'hike'; });
  $('#hikeName').textContent = h.name;
  layers.results.clearLayers(); layers.route.clearLayers(); layers.track.clearLayers();
  setOfflineTiles(true);
  if (h.route) {
    L.polyline(h.route.latlngs, { color: '#d9480f', weight: 6, opacity: 0.75 }).addTo(layers.route);
    L.marker(h.route.latlngs[0], { icon: startIcon, interactive: false }).addTo(layers.route);
    map.fitBounds(L.latLngBounds(h.route.latlngs), { padding: [30, 30] });
  }
  state.trackLine = L.polyline(h.pts.map((p) => [p[0], p[1]]), { color: '#1971c2', weight: 4 }).addTo(layers.track);
  state.follow = true; $('#locate').classList.add('follow');
  setSheet('mid'); updatePauseBtn(); updateHikeUI();
  if (navigator.geolocation) {
    state.watchId = navigator.geolocation.watchPosition(onHikePos, (e) => { $('#gpsDot').className = 'gps-dot'; if (e.code === 1) toast(geoErr(e), 5000); },
      { enableHighAccuracy: true, maximumAge: 0, timeout: 30000 });
  }
  clearInterval(state.timer); state.timer = setInterval(updateHikeUI, 1000);
  requestWake();
}
let lastSave = 0;
function onHikePos(p) {
  const h = state.hike; if (!h) return;
  const c = p.coords, ll = [c.latitude, c.longitude];
  state.hikePos = ll; state.pos = ll; showPos(ll[0], ll[1], c.accuracy);
  $('#gpsDot').className = 'gps-dot ' + (c.accuracy <= 20 ? 'good' : 'weak');
  if (state.follow) map.panTo(ll, { animate: true });
  checkRoute(ll);
  updateHikeUI();
  if (!h.running || c.accuracy > 40) return;
  const last = h.pts[h.pts.length - 1], t = p.timestamp || Date.now();
  if (last) {
    const d = hav(last, ll), dt = (t - last[3]) / 1000;
    if (d < 5) return;
    if (dt > 0 && d / dt > 7 && d > 50) return; // saut GPS irréaliste
    h.distance += d;
  }
  if (c.altitude != null && (c.altitudeAccuracy == null || c.altitudeAccuracy < 25)) {
    if (h.refAlt == null) h.refAlt = c.altitude;
    else if (c.altitude - h.refAlt > 4) { h.ascent += c.altitude - h.refAlt; h.refAlt = c.altitude; }
    else if (h.refAlt - c.altitude > 4) h.refAlt = c.altitude;
  }
  h.pts.push([+ll[0].toFixed(6), +ll[1].toFixed(6), c.altitude != null ? Math.round(c.altitude) : null, t]);
  state.trackLine.addLatLng(ll);
  updateHikeUI();
  if (Date.now() - lastSave > 10000) { saveActive(); lastSave = Date.now(); }
}
function saveActive() { if (!state.hike) return; const { route, cum, ...rest } = state.hike; store.set('activeHike', rest); }
function checkRoute(ll) {
  const h = state.hike; if (!h.route) return;
  const R = h.route.latlngs; let best = Infinity, bi = h.idx;
  const from = Math.max(0, h.idx - 30), to = Math.min(R.length - 1, h.idx + 600);
  for (let i = from; i <= to; i++) { const d = hav(ll, R[i]); if (d < best) { best = d; bi = i; } }
  if (best > 150) { for (let i = 0; i < R.length; i += 3) { const d = hav(ll, R[i]); if (d < best) { best = d; bi = i; } } }
  if (best < 80) h.idx = bi;
  h.off = best;
  h.left = Math.max(0, h.cum.at(-1) - h.cum[h.idx]);
  if (best > 70) banner(`Tu t'éloignes du parcours (${Math.round(best)} m)`); else banner(null);
}
function updateHikeUI() {
  const h = state.hike; if (!h) return;
  const el = h.elapsed + (h.running ? Date.now() - h.resumedAt : 0);
  $('#hTime').textContent = fmtClock(el);
  $('#hDist').textContent = km(h.distance, 2);
  $('#hLeft').textContent = h.route ? (h.left != null ? km(h.left) : km(h.route.distance)) : '–';
  $('#hUp').textContent = Math.round(h.ascent);
  $('#hikeState').textContent = h.running ? 'En cours' : 'En pause';
}
function updatePauseBtn() { $('#hPause').textContent = state.hike && state.hike.running ? 'Pause' : 'Reprendre'; }
$('#hPause').onclick = () => {
  const h = state.hike; if (!h) return;
  if (h.running) { h.elapsed += Date.now() - h.resumedAt; h.running = false; releaseWake(); }
  else { h.resumedAt = Date.now(); h.running = true; requestWake(); }
  saveActive(); updatePauseBtn(); updateHikeUI();
};
$('#hStop').onclick = () => {
  const h = state.hike; if (!h) return;
  if (h.pts.length < 2) { if (!confirm('Presque rien n\'a été enregistré. Arrêter sans sauvegarder ?')) return; endHike(false); return; }
  if (!confirm('Terminer et sauvegarder cette rando ?')) return;
  endHike(true);
};
function simplify(pts, tol) { // Douglas-Peucker approximatif en mètres
  if (pts.length < 3) return pts;
  const keep = new Uint8Array(pts.length); keep[0] = keep[pts.length - 1] = 1;
  const stack = [[0, pts.length - 1]];
  const perp = (p, a, b) => { const ab = hav(a, b); if (ab < 1) return hav(p, a); const s = (hav(a, p) + hav(b, p) + ab) / 2; return 2 * Math.sqrt(Math.max(0, s * (s - ab) * (s - hav(a, p)) * (s - hav(b, p)))) / ab; };
  while (stack.length) { const [i, j] = stack.pop(); let md = 0, mi = -1; for (let k = i + 1; k < j; k++) { const d = perp(pts[k], pts[i], pts[j]); if (d > md) { md = d; mi = k; } } if (md > tol) { keep[mi] = 1; stack.push([i, mi], [mi, j]); } }
  return pts.filter((_, i) => keep[i]);
}
function endHike(save) {
  const h = state.hike;
  if (h.running) h.elapsed += Date.now() - h.resumedAt;
  navigator.geolocation && state.watchId != null && navigator.geolocation.clearWatch(state.watchId);
  clearInterval(state.timer); releaseWake(); banner(null);
  if (save) {
    const entry = { id: h.id, name: h.name, date: h.startedAt, distance: Math.round(h.distance), duration: h.elapsed, ascent: Math.round(h.ascent),
      track: simplify(h.pts, 4).map((p) => [p[0], p[1]]) };
    state.history.unshift(entry); store.set('history', state.history);
  }
  store.del('activeHike'); state.hike = null;
  document.body.classList.remove('hiking'); layers.route.clearLayers();
  setOfflineTiles(false);
  setTab(save ? 'history' : 'routes');
  if (save) toast('Rando sauvegardée 👏');
}

/* ---------- Historique ---------- */
function renderHistory() {
  const box = $('#historyList'), stats = $('#historyStats'); box.innerHTML = '';
  const H = state.history;
  const tot = H.reduce((a, h) => a + h.distance, 0), up = H.reduce((a, h) => a + (h.ascent || 0), 0);
  stats.innerHTML = `<div><b>${H.length}</b><span>randos</span></div><div><b>${km(tot, 0)}</b><span>km au total</span></div><div><b>${up}</b><span>m de montée</span></div>`;
  if (!H.length) { box.innerHTML = '<div class="empty">Tes randos terminées apparaîtront ici.</div>'; return; }
  H.forEach((h) => {
    const el = document.createElement('div'); el.className = 'rcard'; el.style.setProperty('--c', '#1971c2');
    const speed = h.duration > 60000 ? (h.distance / 1000) / (h.duration / 3600000) : 0;
    el.innerHTML = `<div class="rtop"><span class="rname">${esc(h.name)}</span><span class="muted" style="margin:0;font-size:13px">${fmtDate(h.date)}</span></div>
      <div class="rmeta">${km(h.distance, 2)} km · ${fmtDur(h.duration / 60000)} · ↗ ${h.ascent || 0} m${speed ? ' · ' + speed.toFixed(1).replace('.', ',') + ' km/h' : ''}</div>
      <div class="ractions"><button class="secondary" data-act="see">Voir le tracé</button><button class="ghost" data-act="del" aria-label="Supprimer">🗑</button></div>`;
    el.querySelector('[data-act=see]').onclick = () => {
      layers.track.clearLayers();
      if (h.track.length < 2) { toast('Tracé trop court'); return; }
      L.polyline(h.track, { color: '#1971c2', weight: 5 }).addTo(layers.track);
      map.fitBounds(L.latLngBounds(h.track), { padding: [30, 30] }); setSheet('low');
    };
    el.querySelector('[data-act=del]').onclick = () => {
      if (!confirm('Supprimer cette rando de l\'historique ?')) return;
      state.history = state.history.filter((x) => x.id !== h.id); store.set('history', state.history); layers.track.clearLayers(); renderHistory();
    };
    box.appendChild(el);
  });
}

/* ---------- Réglages ---------- */
function renderSettings() {
  $('#keyInput').value = state.settings.key; $('#pace').value = String(state.settings.pace);
  $('#keyStatus').textContent = state.settings.key ? 'Clé enregistrée.' : 'Aucune clé pour l\'instant.';
  const info = $('#storageInfo');
  if (navigator.storage && navigator.storage.estimate) navigator.storage.estimate().then((e) => {
    const off = state.routes.filter((r) => r.offline).length;
    info.textContent = `${off} boucle${off > 1 ? 's' : ''} avec carte hors ligne · ${(e.usage / 1048576).toFixed(0)} Mo utilisés sur le téléphone.`;
  }).catch(() => { info.textContent = ''; });
  else info.textContent = '';
}
$('#keyShow').onclick = () => { const i = $('#keyInput'); i.type = i.type === 'password' ? 'text' : 'password'; };
$('#keySave').onclick = () => { state.settings.key = $('#keyInput').value.trim(); store.set('settings', state.settings); $('#keyStatus').textContent = state.settings.key ? 'Clé enregistrée ✓' : 'Clé effacée.'; };
$('#keyTest').onclick = async () => {
  const key = $('#keyInput').value.trim(); const st = $('#keyStatus');
  if (!key) { st.textContent = 'Colle d\'abord ta clé.'; return; }
  st.textContent = 'Test en cours…';
  try {
    const r = await fetch(ORS_URL, { method: 'POST', headers: { Authorization: key, 'Content-Type': 'application/json' },
      body: JSON.stringify({ coordinates: [[2.3522, 48.8566], [2.3530, 48.8575]] }) });
    st.textContent = r.ok ? 'La clé fonctionne ✓' : (r.status === 401 || r.status === 403) ? 'Clé refusée ✗ Vérifie qu\'elle est complète.' : r.status === 429 ? 'Clé valide, mais limite du jour atteinte.' : 'Réponse inattendue (' + r.status + ').';
    if (r.ok) { state.settings.key = key; store.set('settings', state.settings); }
  } catch (e) { st.textContent = 'Pas de connexion au service. Vérifie ton réseau.'; }
};
$('#pace').onchange = (e) => { state.settings.pace = +e.target.value; store.set('settings', state.settings); };
$('#clearTiles').onclick = async () => {
  if (!confirm('Supprimer toutes les cartes téléchargées ? Tes boucles restent, il faudra juste re-télécharger leur carte.')) return;
  try { await caches.delete(TILE_CACHE); } catch (e) {}
  state.routes.forEach((r) => { r.offline = false; r.tiles = 0; }); store.set('routes', state.routes); renderSettings(); toast('Cartes supprimées');
};

/* ---------- Démarrage ---------- */
function updateNet() { if (state.hike) return; banner(navigator.onLine ? null : 'Hors ligne · tes boucles gardées restent utilisables', 'info'); }
window.addEventListener('online', updateNet); window.addEventListener('offline', updateNet);
const standalone = navigator.standalone || (window.matchMedia && matchMedia('(display-mode: standalone)').matches);
if (!standalone && /iphone|ipad|ipod/i.test(navigator.userAgent)) $('#installTip').hidden = false;
if ('serviceWorker' in navigator && location.protocol === 'https:') navigator.serviceWorker.register('sw.js').catch(() => {});

setSheet('mid'); updateStart(); updateNet();
const active = store.get('activeHike', null);
if (active) { state.hike = active; startHike(null, true); toast('Rando en cours reprise'); }
else { setTab('explore'); locate(true); if (!state.settings.key) setTimeout(() => toast('Première fois ? Ajoute ta clé gratuite dans Réglages', 4000), 1200); }
