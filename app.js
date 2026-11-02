'use strict';
/* Les Boucles de Noune — boucles de randonnée autour de soi, carte hors ligne, enregistrement GPS.
   Tout est stocké sur le téléphone (localStorage + Cache API). */

const ORS_URL = 'https://api.openrouteservice.org/v2/directions/foot-hiking/geojson';
const GEOCODE_URL = 'https://api.openrouteservice.org/geocode/autocomplete';
const OVERPASS_URL = 'https://overpass-api.de/api/interpreter';
const TILE_URL = 'https://data.geopf.fr/wmts?SERVICE=WMTS&REQUEST=GetTile&VERSION=1.0.0&LAYER=GEOGRAPHICALGRIDSYSTEMS.PLANIGNV2&STYLE=normal&FORMAT=image/png&TILEMATRIXSET=PM&TILEMATRIX={z}&TILEROW={y}&TILECOL={x}';
const SAT_URL = 'https://data.geopf.fr/wmts?SERVICE=WMTS&REQUEST=GetTile&VERSION=1.0.0&LAYER=ORTHOIMAGERY.ORTHOPHOTOS&STYLE=normal&FORMAT=image/jpeg&TILEMATRIXSET=PM&TILEMATRIX={z}&TILEROW={y}&TILECOL={x}';
const TILE_CACHE = 'sentiers-tiles-v1';
const OFFLINE_ZOOMS = { bbox: [11, 12, 13, 14], corridor: [15, 16] };
const MAX_TILES = 2500;
const COLORS = ['#d9480f', '#1971c2', '#7048e8', '#2b8a3e', '#c2255c', '#e67700'];
const TRAIL_TYPES = new Set([4, 5, 7, 8]); // ORS waytype : sentier, chemin, piéton, escaliers
const DIRS = ['Nord', 'Nord-Est', 'Est', 'Sud-Est', 'Sud', 'Sud-Ouest', 'Ouest', 'Nord-Ouest'];
// [clé OSM, valeur, emoji, nom, distance max au parcours (m), nombre max]
const POI_TYPES = [
  ['tourism', 'viewpoint', '🔭', 'Point de vue', 150, 20],
  ['natural', 'peak', '⛰️', 'Sommet', 150, 10],
  ['amenity', 'drinking_water', '💧', 'Eau potable', 200, 10],
  ['natural', 'spring', '💧', 'Source', 120, 10],
  ['amenity', 'shelter', '🛖', 'Abri', 150, 10],
  ['tourism', 'picnic_site', '🧺', 'Pique-nique', 120, 10],
  ['amenity', 'toilets', '🚻', 'Toilettes', 150, 6],
  ['amenity', 'bench', '🪑', 'Banc', 40, 25],
  ['amenity', 'parking', '🅿️', 'Parking', 200, 5]
];

/* ---------- Stockage ---------- */
const store = {
  get(k, d) { try { const v = localStorage.getItem('sentiers.' + k); return v == null ? d : JSON.parse(v); } catch (e) { return d; } },
  set(k, v) { try { localStorage.setItem('sentiers.' + k, JSON.stringify(v)); return true; } catch (e) { toast('Mémoire pleine : supprime d\'anciennes randos'); return false; } },
  del(k) { try { localStorage.removeItem('sentiers.' + k); } catch (e) {} }
};

const state = {
  settings: Object.assign({ key: '', pace: 4.5, sos: '', sound: true, base: 'plan', filters: { flat: false, green: false, quiet: false } }, store.get('settings', {})),
  routes: store.get('routes', []),
  history: store.get('history', []),
  places: store.get('places', []),
  pos: null, custom: null, customName: null, results: [], selected: -1,
  hike: null, watchId: null, timer: null, wake: null, follow: true, tab: 'explore'
};
const saveSettings = () => store.set('settings', state.settings);

/* ---------- Utilitaires ---------- */
const $ = (s) => document.querySelector(s);
const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const uid = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 6);
const km = (m, d = 1) => (m / 1000).toFixed(d).replace('.', ',');
function fmtDur(min) { min = Math.round(min); const h = Math.floor(min / 60), m = min % 60; return h ? `${h} h ${String(m).padStart(2, '0')}` : `${m} min`; }
function fmtClock(ms) { const s = Math.floor(ms / 1000); return `${Math.floor(s / 3600)}:${String(Math.floor(s / 60) % 60).padStart(2, '0')}:${String(s % 60).padStart(2, '0')}`; }
function fmtDate(t) { return new Date(t).toLocaleDateString('fr-FR', { weekday: 'short', day: 'numeric', month: 'short' }); }
const RAD = Math.PI / 180;
function hav(a, b) {
  const R = 6371000, dLa = (b[0] - a[0]) * RAD, dLo = (b[1] - a[1]) * RAD;
  const x = Math.sin(dLa / 2) ** 2 + Math.cos(a[0] * RAD) * Math.cos(b[0] * RAD) * Math.sin(dLo / 2) ** 2;
  return 2 * R * Math.asin(Math.sqrt(x));
}
function bearingOf(a, b) {
  const y = Math.sin((b[1] - a[1]) * RAD) * Math.cos(b[0] * RAD);
  const x = Math.cos(a[0] * RAD) * Math.sin(b[0] * RAD) - Math.sin(a[0] * RAD) * Math.cos(b[0] * RAD) * Math.cos((b[1] - a[1]) * RAD);
  return (Math.atan2(y, x) / RAD + 360) % 360;
}
function destPoint(p, brng, d) {
  const la = p[0] * RAD, lo = p[1] * RAD, b = brng * RAD, dr = d / 6371000;
  const la2 = Math.asin(Math.sin(la) * Math.cos(dr) + Math.cos(la) * Math.sin(dr) * Math.cos(b));
  const lo2 = lo + Math.atan2(Math.sin(b) * Math.sin(dr) * Math.cos(la), Math.cos(dr) - Math.sin(la) * Math.sin(la2));
  return [la2 / RAD, lo2 / RAD];
}
function cumDist(ll) { const c = [0]; for (let i = 1; i < ll.length; i++) c.push(c[i - 1] + hav(ll[i - 1], ll[i])); return c; }
function densify(ll, step) {
  const out = [];
  for (let i = 0; i < ll.length; i++) {
    out.push(ll[i]);
    if (i + 1 < ll.length) { const k = Math.floor(hav(ll[i], ll[i + 1]) / step);
      for (let j = 1; j <= k; j++) out.push([ll[i][0] + (ll[i + 1][0] - ll[i][0]) * j / (k + 1), ll[i][1] + (ll[i + 1][1] - ll[i][1]) * j / (k + 1)]); }
  }
  return out;
}
function median(a) { const s = [...a].sort((x, y) => x - y); return s[Math.floor(s.length / 2)]; }
let toastT;
function toast(msg, ms = 2800) { const t = $('#toast'); t.textContent = msg; t.classList.add('show'); clearTimeout(toastT); toastT = setTimeout(() => t.classList.remove('show'), ms); }
function banner(msg, kind) { const b = $('#banner'); if (!msg) { b.hidden = true; return; } b.textContent = msg; b.className = kind || ''; b.hidden = false; }
function estimateMin(dist, ascent) { return (dist / 1000) / state.settings.pace * 60 + (ascent || 0) / 400 * 60; }
function difficulty(dist, ascent) { const e = dist / 1000 + (ascent || 0) / 100; return e < 10 ? 'Facile' : e < 18 ? 'Moyenne' : 'Difficile'; }
function direction(start, ll) {
  let la = 0, lo = 0; ll.forEach((p) => { la += p[0]; lo += p[1]; }); la /= ll.length; lo /= ll.length;
  const ang = Math.atan2((lo - start[1]) * Math.cos(start[0] * RAD), la - start[0]) / RAD;
  return DIRS[Math.round(((ang + 360) % 360) / 45) % 8];
}
function ascentOf(ele) {
  let up = 0, ref = null;
  for (const e of ele) { if (e == null) continue; if (ref == null) ref = e; else if (e - ref > 2) { up += e - ref; ref = e; } else if (ref - e > 2) ref = e; }
  return Math.round(up);
}
function smoothAlt(a, w = 2) { return a.map((v, i) => { if (v == null) return null; let s = 0, n = 0; for (let k = i - w; k <= i + w; k++) if (a[k] != null) { s += a[k]; n++; } return Math.round(s / n); }); }

/* ---------- Carte ---------- */
const view0 = store.get('view', { c: [46.6, 2.4], z: 6 });
const map = L.map('map', {
  zoomControl: false, attributionControl: true,
  rotate: true, touchRotate: true, rotateControl: false, bearing: 0 // rotation à deux doigts (plugin leaflet-rotate)
}).setView(view0.c, view0.z);
const canRotate = typeof map.setBearing === 'function';
map.attributionControl.setPrefix(false);

let tiles = null, offlineMode = false;
function makeTiles() {
  const b = state.settings.base, sat = b === 'sat' && navigator.onLine;
  document.body.classList.toggle('dark-map', b === 'dark');
  if (tiles) map.removeLayer(tiles);
  tiles = L.tileLayer(sat ? SAT_URL : TILE_URL, {
    maxZoom: 18, maxNativeZoom: sat ? 18 : (offlineMode ? 16 : 18), minZoom: 5,
    attribution: '© IGN · © OpenStreetMap', crossOrigin: false
  }).addTo(map);
  document.querySelectorAll('#layerMenu button').forEach((x) => x.classList.toggle('on', x.dataset.base === b));
}
function setOfflineTiles(on) { offlineMode = on; makeTiles(); }
makeTiles();

const layers = { results: L.layerGroup().addTo(map), route: L.layerGroup().addTo(map), track: L.layerGroup().addTo(map),
  arrows: L.layerGroup().addTo(map), pois: L.layerGroup().addTo(map) };
const startIcon = L.divIcon({ className: '', html: '<div class="start-pin"></div>', iconSize: [22, 22], iconAnchor: [11, 11] });
let startMarker = null, posDot = null, posAcc = null;
map.on('moveend', () => store.set('view', { c: [map.getCenter().lat, map.getCenter().lng], z: map.getZoom() }));
map.on('dragstart', () => { if (state.hike) { state.follow = false; $('#locate').classList.remove('follow'); } });

/* Choix du fond de carte */
$('#layersBtn').onclick = (e) => { e.stopPropagation(); $('#layerMenu').hidden = !$('#layerMenu').hidden; };
document.querySelectorAll('#layerMenu button').forEach((b) => (b.onclick = () => {
  state.settings.base = b.dataset.base; saveSettings(); makeTiles(); $('#layerMenu').hidden = true;
  if (b.dataset.base === 'sat') toast(navigator.onLine ? 'Vue satellite (nécessite du réseau)' : 'Satellite indisponible hors ligne, carte normale affichée');
}));
document.addEventListener('click', (e) => { if (!e.target.closest('#layerMenu,#layersBtn')) $('#layerMenu').hidden = true; });

/* Flèches de sens sur le parcours (recalculées selon le zoom) */
let arrowRoute = null;
function setArrows(ll) { arrowRoute = ll && ll.length > 1 ? ll : null; drawArrows(); }
function drawArrows() {
  layers.arrows.clearLayers();
  if (!arrowRoute) return;
  const mpp = 156543.03 * Math.cos(arrowRoute[0][0] * RAD) / 2 ** map.getZoom();
  const spacing = Math.max(120, 140 * mpp), arm = 8 * mpp;
  const cum = cumDist(arrowRoute), total = cum[cum.length - 1];
  let j = 1;
  for (let d = spacing / 2; d < total; d += spacing) {
    while (j < cum.length - 1 && cum[j] < d) j++;
    const a = arrowRoute[j - 1], b = arrowRoute[j], seg = (cum[j] - cum[j - 1]) || 1, t = (d - cum[j - 1]) / seg;
    const p = [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t], br = bearingOf(a, b);
    L.polyline([destPoint(p, br + 145, arm), p, destPoint(p, br - 145, arm)],
      { color: '#fff', weight: 3, opacity: 0.95, interactive: false, lineCap: 'round', lineJoin: 'round' }).addTo(layers.arrows);
  }
}
map.on('zoomend', drawArrows);

/* Points d'intérêt */
function drawPois(pois) {
  layers.pois.clearLayers();
  (pois || []).forEach((p) => {
    const t = POI_TYPES[p.t]; if (!t) return;
    const m = L.marker(p.ll, { icon: L.divIcon({ className: '', html: `<span class="poi">${t[2]}</span>`, iconSize: [26, 26], iconAnchor: [13, 13] }) }).addTo(layers.pois);
    m.on('click', () => toast(t[3] + (p.n ? ' · ' + p.n : '')));
  });
}
async function fetchPois(latlngs) {
  let s = 90, n = -90, w = 180, e = -180;
  latlngs.forEach(([la, lo]) => { s = Math.min(s, la); n = Math.max(n, la); w = Math.min(w, lo); e = Math.max(e, lo); });
  const bb = [s - 0.003, w - 0.004, n + 0.003, e + 0.004].map((v) => v.toFixed(5)).join(',');
  const q = `[out:json][timeout:25];(${POI_TYPES.map(([k, v]) => `nwr["${k}"="${v}"](${bb});`).join('')});out center 600;`;
  const r = await fetch(OVERPASS_URL, { method: 'POST', headers: { 'Content-Type': 'application/x-www-form-urlencoded' }, body: 'data=' + encodeURIComponent(q) });
  if (!r.ok) throw new Error('Overpass ' + r.status);
  const j = await r.json();
  const dense = densify(latlngs, 40), found = POI_TYPES.map(() => []);
  for (const el of j.elements || []) {
    const lat = el.lat != null ? el.lat : el.center && el.center.lat, lon = el.lon != null ? el.lon : el.center && el.center.lon;
    if (lat == null) continue;
    const tg = el.tags || {}, t = POI_TYPES.findIndex(([k, v]) => tg[k] === v); if (t < 0) continue;
    let best = Infinity; for (const p of dense) { const d = hav(p, [lat, lon]); if (d < best) best = d; }
    if (best <= POI_TYPES[t][4]) found[t].push({ t, ll: [+lat.toFixed(6), +lon.toFixed(6)], n: tg.name || '', d: best });
  }
  return found.flatMap((list, t) => list.sort((a, b) => a.d - b.d).slice(0, POI_TYPES[t][5]).map(({ d, ...p }) => p));
}
function poiSummary(pois) {
  if (!pois) return '';
  if (!pois.length) return '<span class="muted">Pas de point d\'intérêt repéré</span>';
  const c = {}; pois.forEach((p) => { const e = POI_TYPES[p.t][2]; c[e] = (c[e] || 0) + 1; });
  return Object.entries(c).map(([e, n]) => `<span>${e} ${n}</span>`).join('');
}
/* Met en avant un parcours : flèches + points d'intérêt */
function focusRoute(ll, pois) { setArrows(ll); drawPois(pois); }
function clearFocus() { setArrows(null); drawPois(null); }

/* ---------- Boussole et rotation ---------- */
const compass = { on: false, smooth: null, last: 0, prog: 0, listening: false };
function setBearingProg(b) { compass.prog = Date.now(); map.setBearing(b); }
function updateNorth() {
  const n = $('#north'); n.hidden = !canRotate;
  if (!canRotate) return;
  n.querySelector('svg').style.transform = `rotate(${map.getBearing()}deg)`;
  n.classList.toggle('active', compass.on);
}
function onOrient(e) {
  let h = e.webkitCompassHeading;
  if (h == null && e.absolute && e.alpha != null) h = 360 - e.alpha;
  if (h == null || isNaN(h)) return;
  const so = (screen.orientation && screen.orientation.angle) || window.orientation || 0;
  h = (h + so + 360) % 360;
  if (compass.smooth == null) compass.smooth = h;
  else { const d = ((h - compass.smooth + 540) % 360) - 180; compass.smooth = (compass.smooth + d * 0.25 + 360) % 360; }
  if (!compass.on || !canRotate) return;
  const now = Date.now(); if (now - compass.last < 100) return;
  const cur = map.getBearing(), diff = ((-compass.smooth - cur + 540) % 360) - 180;
  if (Math.abs(diff) < 2) return;
  compass.last = now; setBearingProg(cur + diff); updateNorth();
}
async function enableCompass() {
  if (typeof DeviceOrientationEvent !== 'undefined' && typeof DeviceOrientationEvent.requestPermission === 'function') {
    try { if (await DeviceOrientationEvent.requestPermission() !== 'granted') { toast('Autorise l\'accès à la boussole pour orienter la carte', 4000); return; } }
    catch (e) { toast('Boussole indisponible'); return; }
  }
  if (!compass.listening) {
    window.addEventListener('deviceorientationabsolute', onOrient, true);
    window.addEventListener('deviceorientation', onOrient, true);
    compass.listening = true;
  }
  compass.on = true; compass.smooth = null; updateNorth();
  toast('Carte orientée dans ton sens de marche');
}
function disableCompass(resetNorth) {
  compass.on = false;
  if (resetNorth && canRotate) setBearingProg(0);
  updateNorth();
}
if (canRotate) {
  map.on('rotate', () => {
    if (compass.on && Date.now() - compass.prog > 400) disableCompass(false); // rotation à la main : on coupe la boussole
    updateNorth();
  });
  $('#north').onclick = () => {
    const b = ((map.getBearing() % 360) + 360) % 360;
    if (compass.on) { disableCompass(true); toast('Nord en haut'); }
    else if (b > 1 && b < 359) { setBearingProg(0); updateNorth(); }
    else enableCompass();
  };
}

function showPos(lat, lng, acc) {
  if (!posDot) {
    posAcc = L.circle([lat, lng], { radius: acc, color: '#1971c2', weight: 1, fillOpacity: 0.1, interactive: false }).addTo(map);
    posDot = L.circleMarker([lat, lng], { radius: 8, color: '#fff', weight: 3, fillColor: '#1971c2', fillOpacity: 1, interactive: false }).addTo(map);
  } else { posDot.setLatLng([lat, lng]); posAcc.setLatLng([lat, lng]).setRadius(acc); }
}

/* ---------- Point de départ ---------- */
function startPoint() { return state.custom || state.pos; }
function updateStart() {
  const s = startPoint();
  $('#startInfo').textContent = state.custom ? 'Départ : ' + (state.customName || 'point choisi sur la carte')
    : (state.pos ? 'Départ : ta position GPS' : 'Départ : ta position GPS (en attente…)');
  if (s) { if (!startMarker) startMarker = L.marker(s, { icon: startIcon, interactive: false }).addTo(map); else startMarker.setLatLng(s); }
}
function setStart(ll, name, pan) {
  state.custom = ll; state.customName = name || null; updateStart(); clearResults();
  if (pan && ll) map.setView(ll, Math.max(map.getZoom(), 14));
}
map.on('click', (e) => {
  if (state.hike || state.tab !== 'explore') return;
  setStart([e.latlng.lat, e.latlng.lng], null, false); toast('Nouveau point de départ');
});
$('#startBtn').onclick = () => { const p = $('#startPanel'); p.hidden = !p.hidden; if (!p.hidden) { renderPlaces(); setSheet('high'); setTimeout(() => $('#addrInput').focus(), 300); } };
$('#useGps').onclick = async () => {
  state.custom = null; state.customName = null; clearResults(); $('#startPanel').hidden = true;
  const p = state.pos || await locate(false); updateStart(); if (p) map.setView(p, Math.max(map.getZoom(), 14));
};
$('#savePlace').onclick = () => {
  const s = startPoint(); if (!s) { toast('Choisis d\'abord un point de départ'); return; }
  const name = (prompt('Nom de ce lieu (ex. Maison, Parking du bois) :', state.customName || '') || '').trim();
  if (!name) return;
  state.places.unshift({ id: uid(), name, ll: [+s[0].toFixed(6), +s[1].toFixed(6)] }); store.set('places', state.places);
  state.custom = s; state.customName = name; updateStart(); renderPlaces(); toast('Lieu enregistré ⭐');
};
function renderPlaces() {
  const box = $('#placesChips'); box.innerHTML = '';
  if (!state.places.length) { box.innerHTML = '<p class="muted small-t">Aucun lieu enregistré. Choisis un départ puis touche « Enregistrer ce départ ».</p>'; return; }
  state.places.forEach((p) => {
    const b = document.createElement('span'); b.className = 'place-chip';
    b.innerHTML = `<button class="pc-go">⭐ ${esc(p.name)}</button><button class="pc-del" aria-label="Supprimer">×</button>`;
    b.querySelector('.pc-go').onclick = () => { setStart(p.ll, p.name, true); $('#startPanel').hidden = true; setSheet('mid'); };
    b.querySelector('.pc-del').onclick = () => { if (!confirm(`Supprimer « ${p.name} » ?`)) return; state.places = state.places.filter((x) => x.id !== p.id); store.set('places', state.places); renderPlaces(); };
    box.appendChild(b);
  });
}
let geoT = null, geoSeq = 0;
$('#addrInput').oninput = (e) => {
  clearTimeout(geoT); const q = e.target.value.trim(), box = $('#addrResults');
  if (q.length < 3) { box.innerHTML = ''; return; }
  geoT = setTimeout(async () => {
    if (!state.settings.key) { box.innerHTML = '<p class="muted small-t">Ajoute ta clé dans Réglages pour chercher une adresse.</p>'; return; }
    if (!navigator.onLine) { box.innerHTML = '<p class="muted small-t">Pas de réseau pour chercher une adresse.</p>'; return; }
    const seq = ++geoSeq; box.innerHTML = '<div class="loading"><span class="spin"></span>Recherche…</div>';
    try {
      const ref = state.pos || [map.getCenter().lat, map.getCenter().lng];
      const u = `${GEOCODE_URL}?api_key=${encodeURIComponent(state.settings.key)}&text=${encodeURIComponent(q)}&boundary.country=FR&size=6&focus.point.lat=${ref[0]}&focus.point.lon=${ref[1]}`;
      const r = await fetch(u); if (!r.ok) throw new Error(r.status);
      const j = await r.json(); if (seq !== geoSeq) return;
      const f = j.features || [];
      if (!f.length) { box.innerHTML = '<p class="muted small-t">Aucun résultat.</p>'; return; }
      box.innerHTML = '';
      f.forEach((x) => {
        const b = document.createElement('button'); b.className = 'addr-item'; b.textContent = x.properties.label;
        b.onclick = () => { const [lon, lat] = x.geometry.coordinates; setStart([lat, lon], x.properties.name || x.properties.label, true); $('#startPanel').hidden = true; $('#addrInput').value = ''; box.innerHTML = ''; setSheet('mid'); };
        box.appendChild(b);
      });
    } catch (err) { if (seq === geoSeq) box.innerHTML = '<p class="muted small-t">Recherche impossible pour le moment.</p>'; }
  }, 400);
};

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
      state.pos = [p.coords.latitude, p.coords.longitude]; state.posAcc = p.coords.accuracy; state.posTime = p.timestamp || Date.now();
      showPos(...state.pos, p.coords.accuracy); updateStart();
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
  layers.track.clearLayers(); clearFocus();
  if (t !== 'explore') layers.results.clearLayers(); else { drawResults(); const r = state.results[state.selected]; if (r) focusRoute(r.latlngs, r.pois); }
  if (t !== 'routes') layers.route.clearLayers();
  if (t === 'routes') renderRoutes();
  if (t === 'history') renderHistory();
  if (t === 'settings') renderSettings();
  if (t === 'explore') updateStart();
  setSheet('mid');
}
document.querySelectorAll('#tabs button').forEach((b) => (b.onclick = () => setTab(b.dataset.tab)));
let sheetMode = 'mid';
function sheetPx(m) { return m === 'low' ? 220 : m === 'high' ? innerHeight * 0.78 : (state.hike ? 370 : innerHeight * 0.46); }
function setSheet(m) {
  sheetMode = m;
  const h = m === 'low' ? '220px' : m === 'high' ? '78dvh' : (state.hike ? '370px' : '46dvh');
  document.documentElement.style.setProperty('--sheet-h', h);
  document.body.classList.toggle('sheet-high', m === 'high');
  setTimeout(() => map.invalidateSize(), 280);
}
$('#handle').onclick = () => setSheet(sheetMode === 'mid' ? 'high' : sheetMode === 'high' ? 'low' : 'mid');
(function () { // glisser le bandeau vers le haut ou le bas
  let y0 = null; const order = ['low', 'mid', 'high'], zone = $('#handle');
  zone.addEventListener('touchstart', (e) => { y0 = e.touches[0].clientY; }, { passive: true });
  zone.addEventListener('touchend', (e) => {
    if (y0 == null) return; const dy = e.changedTouches[0].clientY - y0; y0 = null;
    if (Math.abs(dy) < 25) return;
    const i = order.indexOf(sheetMode); setSheet(order[Math.max(0, Math.min(2, i + (dy < 0 ? 1 : -1)))]);
    e.preventDefault();
  });
})();
function fitTo(latlngs) { // cadre un tracé dans la partie visible au-dessus du bandeau
  if (!latlngs || latlngs.length < 2) return;
  map.fitBounds(L.latLngBounds(latlngs), { paddingTopLeft: [30, 80], paddingBottomRight: [30, sheetPx(sheetMode) + (state.hike ? 0 : 58) + 30] });
}
function revealCard(card) { if (!card) return; setTimeout(() => { $('.sheet-body').scrollTo({ top: card.offsetTop - 6, behavior: 'smooth' }); }, 60); }

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
function syncFilters() { document.querySelectorAll('#filters button').forEach((b) => b.classList.toggle('on', !!state.settings.filters[b.dataset.f])); }
document.querySelectorAll('#filters button').forEach((b) => (b.onclick = () => {
  state.settings.filters[b.dataset.f] = !state.settings.filters[b.dataset.f]; saveSettings(); syncFilters();
  if (state.results.length) $('#search').textContent = 'Relancer avec ces filtres';
}));
syncFilters();

let noWeightings = store.get('noWeightings', false);
async function orsLoop(start, length, seed, points) {
  const f = state.settings.filters, opts = { round_trip: { length: Math.round(length), points, seed } };
  if (!noWeightings && (f.green || f.quiet)) opts.profile_params = { weightings: Object.assign({}, f.green ? { green: 1 } : {}, f.quiet ? { quiet: 1 } : {}) };
  const r = await fetch(ORS_URL, {
    method: 'POST',
    headers: { Authorization: state.settings.key, 'Content-Type': 'application/json', Accept: 'application/geo+json, application/json' },
    body: JSON.stringify({ coordinates: [[start[1], start[0]]], elevation: true, instructions: false, preference: 'recommended', extra_info: ['waytype'], options: opts })
  });
  if (!r.ok) {
    let msg = ''; try { const j = await r.json(); msg = (j.error && (j.error.message || j.error)) || j.message || ''; } catch (e) {}
    if (r.status === 400 && opts.profile_params && !noWeightings) { noWeightings = true; store.set('noWeightings', true); return orsLoop(start, length, seed, points); }
    const err = new Error(typeof msg === 'string' ? msg : 'HTTP ' + r.status); err.status = r.status;
    err.fatal = r.status === 401 || r.status === 403 || r.status === 429; throw err;
  }
  const j = await r.json(); const feat = j.features && j.features[0];
  if (!feat) throw new Error('Réponse vide');
  return parseRoute(feat, start);
}
function parseRoute(f, start) {
  const c = f.geometry.coordinates, s = (f.properties && f.properties.summary) || {};
  const latlngs = c.map((p) => [+p[1].toFixed(6), +p[0].toFixed(6)]);
  const ele = c.map((p) => (p.length > 2 && p[2] != null ? Math.round(p[2]) : null));
  const wt = (f.properties.extras && f.properties.extras.waytype && f.properties.extras.waytype.summary) || [];
  let trail = 0; wt.forEach((w) => { if (TRAIL_TYPES.has(w.value)) trail += w.amount || 0; });
  const distance = s.distance || cumDist(latlngs).at(-1);
  const ascent = s.ascent != null ? Math.round(s.ascent) : ascentOf(ele);
  return { latlngs, ele, distance, ascent, trail: Math.round(trail), start, name: (state.customName ? state.customName + ' · ' : '') + 'Boucle ' + direction(start, latlngs) };
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
    const f = state.settings.filters, target = +distInput.value * 1000, base = Math.floor(Math.random() * 1000);
    let factor = store.get('orsFactor', 0.85); const found = []; let lastErr = null, done = 0;
    for (let b = 0; b < 3 && found.length < 6; b++) {
      const batch = [0, 1, 2].map((i) => ({ seed: base + b * 3 + i, points: (b + i) % 2 ? 4 : 5 }));
      const res = await Promise.all(batch.map((a) => orsLoop(start, target * factor, a.seed, a.points).catch((e) => ({ error: e }))));
      const ratios = [];
      for (const r of res) {
        if (r.error) { lastErr = r.error; if (r.error.fatal) throw r.error; continue; }
        done++; ratios.push(r.distance / (target * factor));
        if (Math.abs(r.distance - target) / target <= 0.3 && !found.some((x) => similar(x, r))) found.push(r);
      }
      if (ratios.length) { factor = Math.min(1.4, Math.max(0.5, 1 / median(ratios))); store.set('orsFactor', factor); }
      box.innerHTML = `<div class="loading"><span class="spin"></span>${found.length} boucle${found.length > 1 ? 's' : ''} trouvée${found.length > 1 ? 's' : ''}…</div>`;
    }
    if (!found.length) {
      box.innerHTML = `<div class="err">${done ? 'Pas de boucle proche de cette distance ici. Essaie une autre distance ou déplace le départ.' : 'Le calcul a échoué' + (lastErr ? ' : ' + esc(lastErr.message) : '') + '.'}</div>`;
      return;
    }
    let list = found;
    if (f.flat) { const flatOnes = found.filter((r) => r.ascent / (r.distance / 1000) <= 30); if (flatOnes.length >= 2) list = flatOnes; }
    const trailW = f.green || f.quiet ? 1.6 : 1;
    list.forEach((r) => {
      r.score = r.trail / 100 * trailW - Math.abs(r.distance - target) / target * 1.5 - (f.flat ? r.ascent / (r.distance / 1000) / 40 : 0);
    });
    list.sort((a, b) => b.score - a.score);
    state.results = list.slice(0, 4).map((r, i) => Object.assign(r, { color: COLORS[i] }));
    state.selected = -1; renderResults(); drawResults(true); setSheet('mid');
  } catch (e) {
    const msg = e.status === 401 || e.status === 403 ? 'Clé refusée. Vérifie-la dans Réglages.'
      : e.status === 429 ? 'Limite gratuite atteinte pour aujourd\'hui. Réessaie plus tard.'
      : 'Impossible de joindre le service de calcul. Vérifie ta connexion.';
    box.innerHTML = `<div class="err">${msg}</div>`;
  } finally { searching = false; btn.disabled = false; btn.textContent = state.results.length ? 'Proposer d\'autres boucles' : 'Proposer des boucles'; }
}
$('#search').onclick = findLoops;

function clearResults() { state.results = []; state.selected = -1; layers.results.clearLayers(); clearFocus(); $('#results').innerHTML = ''; $('#search').textContent = 'Proposer des boucles'; }

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
    <div class="pois-line">${poiSummary(r.pois)}</div>
    ${sparkline(r.ele || [], r.latlngs, color)}${extra || ''}`;
}
function renderResults() {
  const box = $('#results');
  box.innerHTML = '<p class="muted" style="margin-top:14px">Touche une boucle pour la voir sur la carte.</p>';
  state.results.forEach((r, i) => {
    const el = document.createElement('div');
    el.className = 'rcard' + (state.selected === i ? ' sel' : ''); el.style.setProperty('--c', r.color);
    el.innerHTML = routeCardHTML(r, r.color, `<div class="ractions"><button class="secondary" data-act="go">▶ Démarrer</button><button class="primary" data-act="keep">Garder hors ligne</button></div><div class="progress" hidden><i></i></div>`);
    el.onclick = (e) => { if (e.target.closest('button')) return; selectResult(i); };
    el.querySelector('[data-act=keep]').onclick = (e) => keepRoute(r, el, e.currentTarget);
    el.querySelector('[data-act=go]').onclick = () => startDirect(r);
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
  if (fit) fitTo(all);
}
async function loadPois(r) {
  if (r.pois || r.poisLoading || !navigator.onLine) return r.pois;
  r.poisLoading = true;
  try { r.pois = await fetchPois(r.latlngs); } catch (e) { r.pois = null; }
  r.poisLoading = false;
  return r.pois;
}
function selectResult(i) {
  state.selected = state.selected === i ? -1 : i;
  const cards = document.querySelectorAll('#results .rcard');
  cards.forEach((c, k) => c.classList.toggle('sel', k === state.selected));
  drawResults(false);
  if (state.selected >= 0) {
    const r = state.results[i];
    setSheet('low'); fitTo(r.latlngs); revealCard(cards[i]); focusRoute(r.latlngs, r.pois);
    if (!r.pois) loadPois(r).then((p) => {
      if (!p) return;
      const line = cards[i] && cards[i].querySelector('.pois-line'); if (line) line.innerHTML = poiSummary(p);
      if (state.selected === i && state.tab === 'explore') drawPois(p);
    });
  } else { clearFocus(); setSheet('mid'); drawResults(true); }
}

/* ---------- Boucles gardées & tuiles hors ligne ---------- */
function tileUrl(z, x, y) { return TILE_URL.replace('{z}', z).replace('{x}', x).replace('{y}', y); }
function lon2x(lon, z) { return Math.floor((lon + 180) / 360 * 2 ** z); }
function lat2y(lat, z) { const r = lat * RAD; return Math.floor((1 - Math.log(Math.tan(r) + 1 / Math.cos(r)) / Math.PI) / 2 * 2 ** z); }
function tilesFor(latlngs) {
  const set = new Set();
  let s = 90, n = -90, w = 180, e = -180;
  latlngs.forEach(([la, lo]) => { s = Math.min(s, la); n = Math.max(n, la); w = Math.min(w, lo); e = Math.max(e, lo); });
  for (const z of OFFLINE_ZOOMS.bbox) {
    for (let x = lon2x(w, z) - 1; x <= lon2x(e, z) + 1; x++) for (let y = lat2y(n, z) - 1; y <= lat2y(s, z) + 1; y++) set.add(`${z}/${x}/${y}`);
  }
  const dense = densify(latlngs, 60);
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
  const route = { id: uid(), name: r.name, createdAt: Date.now(), latlngs: r.latlngs, ele: r.ele, distance: r.distance, ascent: r.ascent, trail: r.trail, start: r.start, offline: false, tiles: 0, pois: r.pois || null };
  state.routes.unshift(route);
  if (!store.set('routes', state.routes)) { state.routes.shift(); return; }
  r.savedId = route.id;
  btn.disabled = true; btn.textContent = 'Téléchargement de la carte…';
  const bar = card.querySelector('.progress'); bar.hidden = false;
  const poisP = route.pois ? Promise.resolve(route.pois) : loadPois(r);
  await fetchRouteTiles(route, (d, t) => { bar.firstChild.style.width = (d / t * 100) + '%'; });
  route.pois = (await poisP) || route.pois; store.set('routes', state.routes);
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
    el.onclick = (e) => { if (e.target.closest('button')) return; showRoute(r, color, el); };
    el.querySelector('[data-act=go]').onclick = () => { unlockAudio(); startHike(r); };
    el.querySelector('[data-act=del]').onclick = () => {
      if (!confirm(`Supprimer « ${r.name} » ?`)) return;
      state.routes = state.routes.filter((x) => x.id !== r.id); store.set('routes', state.routes); layers.route.clearLayers(); clearFocus(); renderRoutes();
    };
    const dl = el.querySelector('[data-act=dl]');
    if (dl) dl.onclick = async () => {
      if (!navigator.onLine) { toast('Il faut du réseau pour télécharger la carte'); return; }
      dl.disabled = true; dl.textContent = '…'; const bar = el.querySelector('.progress'); bar.hidden = false;
      await fetchRouteTiles(r, (d, t) => { bar.firstChild.style.width = (d / t * 100) + '%'; });
      if (!r.pois) { r.pois = await fetchPois(r.latlngs).catch(() => null); store.set('routes', state.routes); }
      renderRoutes();
    };
    box.appendChild(el);
  });
}
function showRoute(r, color, card) {
  layers.route.clearLayers();
  L.polyline(r.latlngs, { color: color || '#d9480f', weight: 5 }).addTo(layers.route);
  L.marker(r.latlngs[0], { icon: startIcon, interactive: false }).addTo(layers.route);
  setSheet('low'); fitTo(r.latlngs); revealCard(card); focusRoute(r.latlngs, r.pois);
}
$('#freeHike').onclick = () => { unlockAudio(); startHike(null); };

/* ---------- Sons d'alerte ---------- */
let actx = null;
function unlockAudio() {
  try {
    actx = actx || new (window.AudioContext || window.webkitAudioContext)();
    if (actx.state === 'suspended') actx.resume();
    const o = actx.createOscillator(), g = actx.createGain(); g.gain.value = 0.0001; o.connect(g).connect(actx.destination); o.start(); o.stop(actx.currentTime + 0.02);
  } catch (e) {}
}
document.addEventListener('touchend', function once() { unlockAudio(); document.removeEventListener('touchend', once); }, { passive: true });
function beep(pattern) {
  if (!state.settings.sound) return;
  try { if (navigator.audioSession) navigator.audioSession.type = 'transient'; } catch (e) {}
  try {
    if (!actx) unlockAudio(); if (actx.state === 'suspended') actx.resume();
    let t = actx.currentTime + 0.03;
    pattern.forEach(([f, d]) => {
      const o = actx.createOscillator(), g = actx.createGain(); o.type = 'sine'; o.frequency.value = f;
      g.gain.setValueAtTime(0.0001, t); g.gain.exponentialRampToValueAtTime(0.7, t + 0.02); g.gain.exponentialRampToValueAtTime(0.0001, t + d);
      o.connect(g).connect(actx.destination); o.start(t); o.stop(t + d + 0.03); t += d + 0.08;
    });
  } catch (e) {}
  try { navigator.vibrate && navigator.vibrate(pattern.flatMap(([, d]) => [d * 1000, 80])); } catch (e) {}
}
const SND_OFF = [[880, 0.22], [660, 0.22], [880, 0.22], [660, 0.4]];
const SND_BACK = [[660, 0.12], [990, 0.22]];

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

// Démarrer une boucle proposée tout de suite, sans télécharger sa carte
function startDirect(r) {
  const saved = r.savedId && state.routes.find((x) => x.id === r.savedId);
  if (saved) { unlockAudio(); startHike(saved); return; }
  if (!navigator.onLine && !confirm('Pas de réseau : la carte risque de ne pas s\'afficher (le tracé et le GPS fonctionneront). Démarrer quand même ?')) return;
  unlockAudio();
  startHike({ id: null, name: r.name, latlngs: r.latlngs, ele: r.ele, distance: r.distance, ascent: r.ascent, pois: r.pois || null, offline: false });
  if (!r.pois) loadPois(r).then((p) => { if (p && state.hike && state.hike.routeData) { state.hike.routeData.pois = p; drawPois(p); saveActive(); } });
}
function startHike(route, resume) {
  if (state.hike && !resume) return;
  if (!resume) {
    state.hike = { id: uid(), routeId: route ? route.id : null, routeData: route && !route.id ? route : null, name: route ? route.name : 'Rando libre', startedAt: Date.now(),
      elapsed: 0, running: true, resumedAt: Date.now(), pts: [], distance: 0, ascent: 0, refAlt: null, idx: 0 };
    store.set('activeHike', state.hike);
  }
  const h = state.hike;
  h.route = h.routeData || (h.routeId ? state.routes.find((r) => r.id === h.routeId) : null);
  if (h.route) h.cum = cumDist(h.route.latlngs);
  document.body.classList.add('hiking');
  document.querySelectorAll('.view').forEach((v) => { v.hidden = v.dataset.view !== 'hike'; });
  $('#hikeName').textContent = h.name;
  layers.results.clearLayers(); layers.route.clearLayers(); layers.track.clearLayers(); clearFocus();
  setOfflineTiles(!!(h.route && h.route.offline));
  if (h.route && !h.route.offline) setTimeout(() => toast('Carte non téléchargée : elle s\'affichera tant que tu as du réseau', 4500), 800);
  if (h.route) {
    L.polyline(h.route.latlngs, { color: '#d9480f', weight: 6, opacity: 0.8 }).addTo(layers.route);
    L.marker(h.route.latlngs[0], { icon: startIcon, interactive: false }).addTo(layers.route);
    focusRoute(h.route.latlngs, h.route.pois);
  }
  state.trackLine = L.polyline(h.pts.map((p) => [p[0], p[1]]), { color: '#1971c2', weight: 4 }).addTo(layers.track);
  state.follow = true; $('#locate').classList.add('follow');
  setSheet('mid'); updatePauseBtn(); updateHikeUI();
  if (h.route) fitTo(h.route.latlngs);
  if (navigator.geolocation) {
    state.watchId = navigator.geolocation.watchPosition(onHikePos, (e) => { $('#gpsDot').className = 'gps-dot'; if (e.code === 1) toast(geoErr(e), 5000); },
      { enableHighAccuracy: true, maximumAge: 0, timeout: 30000 });
  }
  clearInterval(state.timer); state.timer = setInterval(updateHikeUI, 1000);
  requestWake();
  if (!resume && canRotate && !store.get('compassTip', false)) { store.set('compassTip', true); setTimeout(() => toast('Astuce : touche la boussole pour orienter la carte dans ton sens de marche', 5000), 1500); }
}
let lastSave = 0;
function onHikePos(p) {
  const h = state.hike; if (!h) return;
  const c = p.coords, ll = [c.latitude, c.longitude];
  state.hikePos = ll; state.pos = ll; state.posAcc = c.accuracy; state.posTime = p.timestamp || Date.now();
  showPos(ll[0], ll[1], c.accuracy);
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
  const now = Date.now();
  if (best > 70) {
    banner(`Tu t'éloignes du parcours (${Math.round(best)} m)`);
    if (!h.isOff || now - (h.alertAt || 0) > 45000) { beep(SND_OFF); h.alertAt = now; }
    h.isOff = true;
  } else if (best < 50) {
    if (h.isOff) { beep(SND_BACK); toast('De retour sur le parcours 👍'); }
    h.isOff = false; banner(null);
  }
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
      track: simplify(h.pts, 4).map((p) => [p[0], p[1], p[2]]) };
    state.history.unshift(entry); store.set('history', state.history);
  }
  store.del('activeHike'); state.hike = null;
  document.body.classList.remove('hiking'); layers.route.clearLayers(); clearFocus();
  setOfflineTiles(false);
  setTab(save ? 'history' : 'routes');
  if (save) toast('Rando sauvegardée 👏');
}

/* ---------- SOS ---------- */
function normPhone(s) {
  let d = String(s || '').replace(/[^\d+]/g, '');
  if (/^0\d{9}$/.test(d)) d = '+33' + d.slice(1);
  return d;
}
const isIOS = /iphone|ipad|ipod/i.test(navigator.userAgent) || (navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1);
function buildSms() {
  const num = normPhone(state.settings.sos), p = state.pos, a = $('#sosSms');
  if (!num) { a.removeAttribute('href'); a.classList.add('disabled'); $('#sosPos').textContent = 'Aucun contact d\'urgence. Ajoute son numéro dans Réglages.'; return; }
  a.classList.remove('disabled');
  let body = '🆘 J\'ai besoin d\'aide pendant ma rando.';
  if (p) {
    const t = new Date(state.posTime || Date.now()).toLocaleTimeString('fr-FR', { hour: '2-digit', minute: '2-digit' });
    body += ` Ma position : https://maps.google.com/?q=${p[0].toFixed(5)},${p[1].toFixed(5)} (±${Math.round(state.posAcc || 0)} m, à ${t}).`;
    $('#sosPos').textContent = `Position à ${t}, précision ±${Math.round(state.posAcc || 0)} m.`;
  } else { body += ' (Position GPS introuvable pour le moment.)'; $('#sosPos').textContent = 'Position GPS pas encore trouvée, le SMS partira sans.'; }
  if (state.hike) body += ` Rando : ${state.hike.name}, ${km(state.hike.distance)} km faits.`;
  a.href = `sms:${num}${isIOS ? '&' : '?'}body=${encodeURIComponent(body)}`;
}
$('#sosBtn').onclick = () => {
  $('#sosModal').hidden = false;
  $('#sosTo').textContent = state.settings.sos ? 'Envoyé à ' + state.settings.sos : '';
  $('#sosPos').textContent = 'Localisation en cours…';
  buildSms();
  if (navigator.geolocation) navigator.geolocation.getCurrentPosition((p) => {
    state.pos = [p.coords.latitude, p.coords.longitude]; state.posAcc = p.coords.accuracy; state.posTime = p.timestamp || Date.now(); buildSms();
  }, () => buildSms(), { enableHighAccuracy: true, timeout: 10000, maximumAge: 60000 });
};
$('#sosClose').onclick = () => { $('#sosModal').hidden = true; };
$('#sosSettings').onclick = () => { $('#sosModal').hidden = true; if (!state.hike) setTab('settings'); };

/* ---------- Historique & statistiques ---------- */
function renderHistory() {
  const box = $('#historyList'), stats = $('#historyStats'); box.innerHTML = '';
  const H = state.history;
  const tot = H.reduce((a, h) => a + h.distance, 0), up = H.reduce((a, h) => a + (h.ascent || 0), 0);
  stats.innerHTML = `<div><b>${H.length}</b><span>randos</span></div><div><b>${km(tot, 0)}</b><span>km au total</span></div><div><b>${up}</b><span>m de montée</span></div>`;
  renderInsights(H);
  if (!H.length) { box.innerHTML = '<div class="empty">Tes randos terminées apparaîtront ici.</div>'; return; }
  H.forEach((h) => {
    const el = document.createElement('div'); el.className = 'rcard'; el.style.setProperty('--c', '#1971c2');
    const speed = h.duration > 60000 ? (h.distance / 1000) / (h.duration / 3600000) : 0;
    const alts = h.track.map((p) => (p.length > 2 ? p[2] : null)), hasAlt = alts.filter((a) => a != null).length >= 5;
    el.innerHTML = `<div class="rtop"><span class="rname">${esc(h.name)}</span><span class="muted" style="margin:0;font-size:13px">${fmtDate(h.date)}</span></div>
      <div class="rmeta">${km(h.distance, 2)} km · ${fmtDur(h.duration / 60000)} · ↗ ${h.ascent || 0} m${speed ? ' · ' + speed.toFixed(1).replace('.', ',') + ' km/h' : ''}</div>
      ${hasAlt ? sparkline(smoothAlt(alts), h.track, '#1971c2') : ''}
      <div class="ractions"><button class="secondary" data-act="see">Voir le tracé</button><button class="ghost" data-act="del" aria-label="Supprimer">🗑</button></div>`;
    el.querySelector('[data-act=see]').onclick = () => {
      layers.track.clearLayers();
      if (h.track.length < 2) { toast('Tracé trop court'); return; }
      L.polyline(h.track.map((p) => [p[0], p[1]]), { color: '#1971c2', weight: 5 }).addTo(layers.track);
      setSheet('low'); fitTo(h.track); revealCard(el); setArrows(h.track.map((p) => [p[0], p[1]]));
    };
    el.querySelector('[data-act=del]').onclick = () => {
      if (!confirm('Supprimer cette rando de l\'historique ?')) return;
      state.history = state.history.filter((x) => x.id !== h.id); store.set('history', state.history); layers.track.clearLayers(); clearFocus(); renderHistory();
    };
    box.appendChild(el);
  });
}
function renderInsights(H) {
  const box = $('#insights');
  if (!H.length) { box.innerHTML = ''; return; }
  const now = new Date(), months = [];
  for (let i = 5; i >= 0; i--) { const d = new Date(now.getFullYear(), now.getMonth() - i, 1); months.push({ y: d.getFullYear(), m: d.getMonth(), km: 0, n: 0 }); }
  H.forEach((h) => { const d = new Date(h.date), mo = months.find((x) => x.y === d.getFullYear() && x.m === d.getMonth()); if (mo) { mo.km += h.distance / 1000; mo.n++; } });
  const max = Math.max(1, ...months.map((m) => m.km));
  const bars = months.map((m) => {
    const lab = new Date(m.y, m.m, 1).toLocaleDateString('fr-FR', { month: 'short' }).replace('.', '');
    return `<div class="mbar"><span class="mval">${m.km ? m.km.toFixed(m.km < 10 ? 1 : 0).replace('.', ',') : ''}</span><i style="height:${Math.max(m.km ? 4 : 0, m.km / max * 70)}px"></i><span class="mlab">${lab}</span></div>`;
  }).join('');
  const longest = H.reduce((a, h) => (h.distance > a.distance ? h : a));
  const climb = H.reduce((a, h) => ((h.ascent || 0) > (a.ascent || 0) ? h : a));
  const fast = H.filter((h) => h.distance >= 2000 && h.duration > 600000).reduce((a, h) => { const s = h.distance / h.duration; return !a || s > a.distance / a.duration ? h : a; }, null);
  const totalTime = H.reduce((a, h) => a + h.duration, 0);
  const thisMonth = months[5];
  box.innerHTML = `<div class="card insights">
    <h2>Ce mois-ci : ${km(thisMonth.km * 1000)} km · ${thisMonth.n} rando${thisMonth.n > 1 ? 's' : ''}</h2>
    <div class="mbars">${bars}</div>
    <div class="records">
      <div>🏆 Plus longue<br><b>${km(longest.distance)} km</b><small>${fmtDate(longest.date)}</small></div>
      <div>⛰️ Plus de montée<br><b>${climb.ascent || 0} m</b><small>${fmtDate(climb.date)}</small></div>
      <div>⚡ Plus rapide<br><b>${fast ? (fast.distance / fast.duration * 3600).toFixed(1).replace('.', ',') + ' km/h' : '–'}</b><small>${fast ? fmtDate(fast.date) : ''}</small></div>
      <div>⏱️ Temps de marche<br><b>${fmtDur(totalTime / 60000)}</b><small>au total</small></div>
    </div></div>`;
}

/* ---------- Réglages ---------- */
function renderSettings() {
  $('#keyInput').value = state.settings.key; $('#pace').value = String(state.settings.pace);
  $('#keyStatus').textContent = state.settings.key ? 'Clé enregistrée.' : 'Aucune clé pour l\'instant.';
  $('#sosInput').value = state.settings.sos || ''; $('#soundToggle').checked = !!state.settings.sound;
  const info = $('#storageInfo');
  if (navigator.storage && navigator.storage.estimate) navigator.storage.estimate().then((e) => {
    const off = state.routes.filter((r) => r.offline).length;
    info.textContent = `${off} boucle${off > 1 ? 's' : ''} avec carte hors ligne · ${(e.usage / 1048576).toFixed(0)} Mo utilisés sur le téléphone.`;
  }).catch(() => { info.textContent = ''; });
  else info.textContent = '';
}
$('#keyShow').onclick = () => { const i = $('#keyInput'); i.type = i.type === 'password' ? 'text' : 'password'; };
$('#keySave').onclick = () => { state.settings.key = $('#keyInput').value.trim(); saveSettings(); $('#keyStatus').textContent = state.settings.key ? 'Clé enregistrée ✓' : 'Clé effacée.'; };
$('#keyTest').onclick = async () => {
  const key = $('#keyInput').value.trim(); const st = $('#keyStatus');
  if (!key) { st.textContent = 'Colle d\'abord ta clé.'; return; }
  st.textContent = 'Test en cours…';
  try {
    const r = await fetch(ORS_URL, { method: 'POST', headers: { Authorization: key, 'Content-Type': 'application/json' },
      body: JSON.stringify({ coordinates: [[2.3522, 48.8566], [2.3530, 48.8575]] }) });
    st.textContent = r.ok ? 'La clé fonctionne ✓' : (r.status === 401 || r.status === 403) ? 'Clé refusée ✗ Vérifie qu\'elle est complète.' : r.status === 429 ? 'Clé valide, mais limite du jour atteinte.' : 'Réponse inattendue (' + r.status + ').';
    if (r.ok) { state.settings.key = key; saveSettings(); }
  } catch (e) { st.textContent = 'Pas de connexion au service. Vérifie ton réseau.'; }
};
$('#sosSave').onclick = () => {
  const v = $('#sosInput').value.trim();
  if (v && normPhone(v).replace(/\D/g, '').length < 8) { $('#sosStatus').textContent = 'Numéro incomplet.'; return; }
  state.settings.sos = v; saveSettings(); $('#sosStatus').textContent = v ? 'Contact d\'urgence enregistré ✓' : 'Contact effacé.';
};
$('#soundToggle').onchange = (e) => { state.settings.sound = e.target.checked; saveSettings(); if (e.target.checked) { unlockAudio(); beep(SND_BACK); } };
$('#soundTest').onclick = () => { unlockAudio(); const s = state.settings.sound; state.settings.sound = true; beep(SND_OFF); state.settings.sound = s; };
$('#pace').onchange = (e) => { state.settings.pace = +e.target.value; saveSettings(); };
$('#clearTiles').onclick = async () => {
  if (!confirm('Supprimer toutes les cartes téléchargées ? Tes boucles restent, il faudra juste re-télécharger leur carte.')) return;
  try { await caches.delete(TILE_CACHE); } catch (e) {}
  state.routes.forEach((r) => { r.offline = false; r.tiles = 0; }); store.set('routes', state.routes); renderSettings(); toast('Cartes supprimées');
};

/* ---------- Démarrage ---------- */
function updateNet() { if (!state.hike) banner(navigator.onLine ? null : 'Hors ligne · tes boucles gardées restent utilisables', 'info'); if (state.settings.base === 'sat') makeTiles(); }
window.addEventListener('online', updateNet); window.addEventListener('offline', updateNet);
const standalone = navigator.standalone || (window.matchMedia && matchMedia('(display-mode: standalone)').matches);
if (!standalone && isIOS) $('#installTip').hidden = false;
if ('serviceWorker' in navigator && location.protocol === 'https:') {
  const hadController = !!navigator.serviceWorker.controller;
  navigator.serviceWorker.register('sw.js').then((reg) => reg.update()).catch(() => {});
  let reloaded = false; // nouvelle version installée : on recharge pour l'utiliser tout de suite (sauf en pleine rando)
  navigator.serviceWorker.addEventListener('controllerchange', () => {
    if (!hadController || reloaded) return;
    if (state.hike) { toast('Mise à jour prête : elle s\'appliquera après la rando'); return; }
    reloaded = true; location.reload();
  });
}
updateNorth();
setSheet('mid'); updateStart(); updateNet();
const active = store.get('activeHike', null);
if (active) { state.hike = active; startHike(null, true); toast('Rando en cours reprise'); }
else { setTab('explore'); locate(true); if (!state.settings.key) setTimeout(() => toast('Première fois ? Ajoute ta clé gratuite dans Réglages', 4000), 1200); }
