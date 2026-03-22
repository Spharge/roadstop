'use strict';

// ─── Constants ────────────────────────────────────────────────────────────────
const OVERPASS_URL = 'https://overpass-api.de/api/interpreter';
const OSRM_URL     = 'https://router.project-osrm.org/route/v1/driving';
const CLUSTER_RADIUS_KM  = 0.35;   // merge stops within this distance
const HEADING_TOLERANCE  = 80;     // ±degrees from heading to include
const CACHE_DURATION_MS  = 15 * 60 * 1000;
const SIGNIFICANT_MOVE_KM = 4;     // re-query after moving this far

// ─── State ────────────────────────────────────────────────────────────────────
const state = {
  lat: null, lng: null,
  heading: null,
  headingSource: null,       // 'gps' | 'compass' | null
  rangeMiles: 50,
  activeAmenities: new Set(['restrooms', 'fuel', 'food', 'ev', 'dogpark']),
  stops: [],
  lastQueryLat: null, lastQueryLng: null, lastQueryTime: null,
  lastQueryRangeMiles: null,
  isLoading: false,
  isStale: false,
  compassListening: false,
  searchMode: 'miles',    // 'miles' | 'time'
  timeMinutes: 60,        // selected look-ahead time
  speedHistory: [],       // recent GPS speeds in mph (for rolling average)
  routeSearch: false,     // narrow search to projected route corridor
  milesFromRoute: 2,      // half-width of corridor in miles
  map: null,
  mapMarkers: [],
  userMarker: null,
  searchLayer: null,      // Leaflet layer showing search area
  routePolyline: null,    // [[lat,lng]…] from OSRM when route search is active
  activeView: 'list',
};

// ─── Geo Math ─────────────────────────────────────────────────────────────────
function toRad(d) { return d * Math.PI / 180; }
function toDeg(r) { return r * 180 / Math.PI; }

function haversineKm(lat1, lng1, lat2, lng2) {
  const R = 6371;
  const dLat = toRad(lat2 - lat1), dLng = toRad(lng2 - lng1);
  const a = Math.sin(dLat / 2) ** 2 +
            Math.cos(toRad(lat1)) * Math.cos(toRad(lat2)) * Math.sin(dLng / 2) ** 2;
  return R * 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a));
}

function bearing(lat1, lng1, lat2, lng2) {
  const dLng = toRad(lng2 - lng1);
  const y = Math.sin(dLng) * Math.cos(toRad(lat2));
  const x = Math.cos(toRad(lat1)) * Math.sin(toRad(lat2)) -
            Math.sin(toRad(lat1)) * Math.cos(toRad(lat2)) * Math.cos(dLng);
  return (toDeg(Math.atan2(y, x)) + 360) % 360;
}

function movePoint(lat, lng, headingDeg, distKm) {
  const R = 6371, d = distKm / R, h = toRad(headingDeg);
  const lat1 = toRad(lat), lng1 = toRad(lng);
  const lat2 = Math.asin(Math.sin(lat1) * Math.cos(d) + Math.cos(lat1) * Math.sin(d) * Math.cos(h));
  const lng2 = lng1 + Math.atan2(Math.sin(h) * Math.sin(d) * Math.cos(lat1),
                                   Math.cos(d) - Math.sin(lat1) * Math.sin(lat2));
  return { lat: toDeg(lat2), lng: toDeg(lng2) };
}

function bboxAround(lat, lng, radiusKm) {
  const R = 6371;
  const dLat = toDeg(radiusKm / R);
  const dLng = toDeg(radiusKm / R / Math.cos(toRad(lat)));
  return { south: lat - dLat, north: lat + dLat, west: lng - dLng, east: lng + dLng };
}

function isAhead(userHeading, bearingToStop) {
  if (userHeading === null) return true;
  let diff = ((bearingToStop - userHeading) + 360) % 360;
  if (diff > 180) diff = 360 - diff;
  return diff <= HEADING_TOLERANCE;
}

function headingToCardinal(deg) {
  return ['N','NE','E','SE','S','SW','W','NW'][Math.round(deg / 45) % 8];
}

function kmToMiles(km) { return km * 0.621371; }

// ─── Polyline Geometry ────────────────────────────────────────────────────────

// Minimum distance (km) from a point to a line segment, using lat/lng dot-product
// projection (accurate enough at road-corridor scale)
function pointToSegmentDistanceKm(lat, lng, lat1, lng1, lat2, lng2) {
  const denom = (lat2 - lat1) ** 2 + (lng2 - lng1) ** 2;
  if (denom === 0) return haversineKm(lat, lng, lat1, lng1);
  const t = Math.max(0, Math.min(1,
    ((lat - lat1) * (lat2 - lat1) + (lng - lng1) * (lng2 - lng1)) / denom
  ));
  return haversineKm(lat, lng, lat1 + t * (lat2 - lat1), lng1 + t * (lng2 - lng1));
}

function pointToPolylineDistanceKm(lat, lng, polyline) {
  let min = Infinity;
  for (let i = 0; i < polyline.length - 1; i++) {
    const d = pointToSegmentDistanceKm(lat, lng,
      polyline[i][0], polyline[i][1], polyline[i + 1][0], polyline[i + 1][1]);
    if (d < min) min = d;
  }
  return min;
}

// Build a filled polygon corridor around a polyline for map visualization
function polylineCorridorPolygon(polyline, widthKm) {
  const left = [], right = [];
  for (let i = 0; i < polyline.length; i++) {
    const [lat, lng] = polyline[i];
    const hdg = i < polyline.length - 1
      ? bearing(lat, lng, polyline[i + 1][0], polyline[i + 1][1])
      : bearing(polyline[i - 1][0], polyline[i - 1][1], lat, lng);
    left.push(movePoint(lat, lng, (hdg + 270) % 360, widthKm));
    right.push(movePoint(lat, lng, (hdg + 90)  % 360, widthKm));
  }
  return left.concat(right.reverse()).map(p => [p.lat, p.lng]);
}

// Cross-track distance: perpendicular km from a point to a great-circle path
function crossTrackDistanceKm(lat, lng, originLat, originLng, headingDeg) {
  const R = 6371;
  const d13 = haversineKm(originLat, originLng, lat, lng);
  if (d13 === 0) return 0;
  const θ13 = toRad(bearing(originLat, originLng, lat, lng));
  const θ12 = toRad(headingDeg);
  return Math.abs(Math.asin(Math.sin(d13 / R) * Math.sin(θ13 - θ12))) * R;
}

function getAverageSpeedMph() {
  if (state.speedHistory.length === 0) return null;
  return state.speedHistory.reduce((a, b) => a + b, 0) / state.speedHistory.length;
}

function getEffectiveRangeMiles() {
  if (state.searchMode === 'miles') return state.rangeMiles;
  const speed = getAverageSpeedMph() || 55; // fallback to 55 mph if no data yet
  return Math.max(10, Math.round(speed * state.timeMinutes / 60));
}

// ─── Amenity Detection ────────────────────────────────────────────────────────
const AMENITY_META = {
  restrooms: { icon: '🚻', label: 'Restrooms' },
  fuel:      { icon: '⛽', label: 'Gas'       },
  food:      { icon: '🍔', label: 'Food'      },
  ev:        { icon: '⚡', label: 'EV'        },
  dogpark:   { icon: '🐕', label: 'Dog Park'  },
};

const TYPE_ICON = {
  rest_area:        '🛣️',
  services:         '🏪',
  fuel:             '⛽',
  fast_food:        '🍔',
  restaurant:       '🍽️',
  cafe:             '☕',
  charging_station: '⚡',
  toilets:          '🚻',
  dog_park:         '🐕',
};

function detectAmenities(tags) {
  const a = new Set();
  const hw = tags.highway, am = tags.amenity, le = tags.leisure;

  if (am === 'toilets' || tags.toilets === 'yes' || hw === 'rest_area') a.add('restrooms');
  if (am === 'fuel'    || tags.fuel    === 'yes')                        a.add('fuel');
  if (['fast_food','restaurant','cafe','food_court','bar'].includes(am) || tags.food === 'yes') a.add('food');
  if (am === 'charging_station')                                          a.add('ev');
  if (le === 'dog_park' || am === 'dog_park')                             a.add('dogpark');

  // Service areas typically have restrooms, fuel, and food
  if (hw === 'services') {
    a.add('restrooms');
    if (tags.fuel !== 'no')  a.add('fuel');
    if (tags.food !== 'no')  a.add('food');
  }
  return a;
}

function getStopName(tags) {
  if (tags.name) return tags.name;
  if (tags.highway === 'rest_area') return 'Rest Area';
  if (tags.highway === 'services')  return 'Service Area';
  const am = tags.amenity;
  if (am === 'fuel')             return tags.brand || 'Gas Station';
  if (am === 'fast_food')        return tags.brand || 'Fast Food';
  if (am === 'restaurant')       return 'Restaurant';
  if (am === 'cafe')             return 'Café';
  if (am === 'charging_station') return tags.brand || 'EV Charging';
  if (am === 'toilets')          return 'Restrooms';
  if (tags.leisure === 'dog_park') return 'Dog Park';
  return 'Stop';
}

function getStopType(tags) {
  if (tags.highway === 'rest_area') return 'rest_area';
  if (tags.highway === 'services')  return 'services';
  return tags.amenity || tags.leisure || 'stop';
}

// ─── Clustering ───────────────────────────────────────────────────────────────
function clusterStops(stops) {
  const clusters = [], processed = new Set();
  for (let i = 0; i < stops.length; i++) {
    if (processed.has(i)) continue;
    const c = { ...stops[i], amenities: new Set(stops[i].amenities) };
    processed.add(i);
    for (let j = i + 1; j < stops.length; j++) {
      if (processed.has(j)) continue;
      if (haversineKm(c.lat, c.lng, stops[j].lat, stops[j].lng) < CLUSTER_RADIUS_KM) {
        stops[j].amenities.forEach(a => c.amenities.add(a));
        // Prefer names from dedicated rest/service areas
        const isHigherPriority = stops[j].type === 'rest_area' || stops[j].type === 'services';
        if ((!c.name || isHigherPriority) && stops[j].name) {
          c.name = stops[j].name;
          c.type = stops[j].type;
        }
        processed.add(j);
      }
    }
    c.amenities = Array.from(c.amenities);
    clusters.push(c);
  }
  return clusters;
}

// ─── Retry / Stale helpers ────────────────────────────────────────────────────
let retryTimer = null;

function scheduleRetry() {
  clearTimeout(retryTimer);
  retryTimer = setTimeout(() => fetchStops(), 12000); // retry after 12 s
}

function clearRetry() {
  clearTimeout(retryTimer);
  retryTimer = null;
}

function setStaleIndicator(visible) {
  state.isStale = visible;
  const el = document.getElementById('stale-indicator');
  if (el) el.style.display = visible ? 'inline-flex' : 'none';
}

// ─── OSRM Route ───────────────────────────────────────────────────────────────
// Fetches the actual road geometry ahead via OSRM and stores it in state.routePolyline.
// Falls back gracefully (leaves routePolyline null) on any error.
async function fetchRoutePolyline() {
  if (state.lat === null || state.heading === null) return;
  const rangeKm = getEffectiveRangeMiles() * 1.60934;
  const end     = movePoint(state.lat, state.lng, state.heading, rangeKm);
  const url     = `${OSRM_URL}/${state.lng},${state.lat};${end.lng},${end.lat}?overview=full&geometries=geojson`;
  try {
    const resp = await fetch(url);
    if (!resp.ok) return;
    const data   = await resp.json();
    const coords = data.routes?.[0]?.geometry?.coordinates;
    if (coords?.length > 1) {
      // GeoJSON uses [lng, lat] — swap to [lat, lng] for internal use
      state.routePolyline = coords.map(([lng, lat]) => [lat, lng]);
    }
  } catch (e) {
    console.warn('OSRM fetch failed — falling back to straight-line corridor:', e);
  }
}

// ─── Overpass API ─────────────────────────────────────────────────────────────
async function fetchStops() {
  if (!state.lat || !state.lng || state.isLoading) return;

  const rangeKm = getEffectiveRangeMiles() * 1.60934;
  // Center the bounding box halfway ahead of the user in their direction of travel
  const center = state.heading !== null
    ? movePoint(state.lat, state.lng, state.heading, rangeKm * 0.5)
    : { lat: state.lat, lng: state.lng };

  const { south, west, north, east } = bboxAround(center.lat, center.lng, rangeKm * 0.65);
  const bb = `${south},${west},${north},${east}`;

  const query = `[out:json][timeout:30];
(
  node["highway"="rest_area"](${bb});
  way["highway"="rest_area"](${bb});
  node["highway"="services"](${bb});
  way["highway"="services"](${bb});
  node["amenity"="toilets"]["access"!="private"](${bb});
  node["amenity"="fuel"]["access"!="private"](${bb});
  node["amenity"="fast_food"](${bb});
  node["amenity"="restaurant"](${bb});
  node["amenity"="cafe"](${bb});
  node["amenity"="charging_station"](${bb});
  node["leisure"="dog_park"](${bb});
);
out center;`;

  state.isLoading = true;
  const hadStops = state.stops.length > 0;
  if (!hadStops) showLoading(); // only show spinner when the list is empty

  try {
    // Fire Overpass and (if route search is on) OSRM in parallel
    const [resp] = await Promise.all([
      fetch(OVERPASS_URL, {
        method: 'POST',
        headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
        body: `data=${encodeURIComponent(query)}`,
      }),
      state.routeSearch && state.heading !== null
        ? fetchRoutePolyline()
        : Promise.resolve(),
    ]);

    // 429 = rate limited — keep the current list, mark stale, retry silently
    if (resp.status === 429) {
      setStaleIndicator(true);
      scheduleRetry();
      return;
    }

    if (!resp.ok) throw new Error(`Server error ${resp.status}`);
    const data = await resp.json();

    const raw = data.elements
      .filter(el => el.tags)
      .map(el => ({
        lat:      el.type === 'way' ? el.center.lat : el.lat,
        lng:      el.type === 'way' ? el.center.lon : el.lon,
        name:     getStopName(el.tags),
        type:     getStopType(el.tags),
        amenities: Array.from(detectAmenities(el.tags)),
      }))
      .filter(s => s.amenities.length > 0);

    const clustered = clusterStops(raw);

    state.stops = clustered
      .map(s => ({
        ...s,
        distanceKm: haversineKm(state.lat, state.lng, s.lat, s.lng),
        bearing:    bearing(state.lat, state.lng, s.lat, s.lng),
      }))
      .filter(s => isAhead(state.heading, s.bearing))
      .filter(s => {
        if (!state.routeSearch || state.heading === null) return true;
        const corridorKm = state.milesFromRoute * 1.60934;
        if (state.routePolyline) {
          // Use actual road geometry from OSRM
          return pointToPolylineDistanceKm(s.lat, s.lng, state.routePolyline) <= corridorKm;
        }
        // Fallback: straight-line cross-track filter
        return crossTrackDistanceKm(s.lat, s.lng, state.lat, state.lng, state.heading) <= corridorKm;
      })
      .sort((a, b) => a.distanceKm - b.distanceKm);

    state.lastQueryLat        = state.lat;
    state.lastQueryLng        = state.lng;
    state.lastQueryTime       = Date.now();
    state.lastQueryRangeMiles = getEffectiveRangeMiles();

    clearRetry();
    setStaleIndicator(false);
    renderStops();
  } catch (err) {
    console.error('Overpass error:', err);
    if (!hadStops) showError(err.message);
    else setStaleIndicator(true); // keep existing list, flag as stale
  } finally {
    state.isLoading = false;
  }
}

function shouldRefetch() {
  if (!state.lastQueryTime) return true;
  if (Date.now() - state.lastQueryTime > CACHE_DURATION_MS) return true;
  if (state.lastQueryLat !== null) {
    if (haversineKm(state.lastQueryLat, state.lastQueryLng, state.lat, state.lng) > SIGNIFICANT_MOVE_KM) return true;
  }
  // Re-fetch if the effective range drifted by more than 5 miles (e.g. speed changed in time mode)
  if (state.lastQueryRangeMiles !== null) {
    if (Math.abs(getEffectiveRangeMiles() - state.lastQueryRangeMiles) > 5) return true;
  }
  return false;
}

// ─── UI ───────────────────────────────────────────────────────────────────────
function updateFiltersSummary() {
  const el = document.getElementById('filters-summary');
  if (!el) return;

  const total = Object.keys(AMENITY_META).length;
  const active = state.activeAmenities.size;
  const amenityStr = active === total ? 'All amenities' : `${active} amenit${active === 1 ? 'y' : 'ies'}`;

  let rangeStr;
  if (state.searchMode === 'miles') {
    rangeStr = `${state.rangeMiles} mi`;
  } else {
    const h = Math.floor(state.timeMinutes / 60);
    const m = state.timeMinutes % 60;
    rangeStr = h > 0 ? (m > 0 ? `${h}h ${m}m` : `${h}h`) : `${m}m`;
  }

  const routeStr = state.routeSearch ? ` · Route ±${state.milesFromRoute} mi` : '';
  el.textContent = `${amenityStr} · ${rangeStr}${routeStr}`;
}

function updateRangeLabel() {
  const el = document.getElementById('range-label');
  if (!el) return;
  const prefix = state.heading !== null ? 'Search ahead' : 'Search radius';

  if (state.searchMode === 'miles') {
    el.innerHTML = `${prefix}: <strong>${state.rangeMiles} mi</strong>`;
  } else {
    const speedMph      = getAverageSpeedMph();
    const effectiveMph  = speedMph || 55;
    const distMi        = Math.round(effectiveMph * state.timeMinutes / 60);
    const h             = Math.floor(state.timeMinutes / 60);
    const m             = state.timeMinutes % 60;
    const timeStr       = h > 0 ? (m > 0 ? `${h}h ${m}m` : `${h}h`) : `${m}m`;
    const speedLabel    = speedMph ? `${Math.round(speedMph)} mph` : '55 mph est.';
    el.innerHTML = `${prefix}: <strong>${timeStr}</strong> <span class="speed-hint">≈${distMi} mi @ ${speedLabel}</span>`;
  }
}

function setSearchMode(mode) {
  state.searchMode = mode;
  const slider = document.getElementById('range-slider');
  document.getElementById('miles-mode-btn').classList.toggle('active', mode === 'miles');
  document.getElementById('time-mode-btn').classList.toggle('active', mode === 'time');
  if (mode === 'miles') {
    slider.min = 10; slider.max = 150; slider.step = 10; slider.value = state.rangeMiles;
  } else {
    slider.min = 15; slider.max = 180; slider.step = 15; slider.value = state.timeMinutes;
  }
  updateRangeLabel();
  state.lastQueryTime = null;
  fetchStops();
}

function getFilteredStops() {
  return state.stops.filter(s => s.amenities.some(a => state.activeAmenities.has(a)));
}

function renderStops() {
  const list = document.getElementById('stops-list');
  const filtered = getFilteredStops();

  if (filtered.length === 0) {
    list.innerHTML = `
      <div class="status-message">
        <span class="status-icon">🔍</span>
        <p>No stops found ahead matching your filters.</p>
        <p class="hint">Try increasing the search range or selecting more amenities.</p>
      </div>`;
    if (state.activeView === 'map') renderMap();
    return;
  }

  list.innerHTML = filtered.map((stop, i) => {
    const num       = i + 1;
    const distMi    = kmToMiles(stop.distanceKm).toFixed(1);
    const icon      = TYPE_ICON[stop.type] || '📍';
    const mapsUrl   = `https://maps.apple.com/?daddr=${stop.lat},${stop.lng}&dirflg=d`;
    const googleUrl = `https://www.google.com/maps/search/${encodeURIComponent(stop.name)}/@${stop.lat},${stop.lng},16z`;

    const badges = stop.amenities
      .filter(a => AMENITY_META[a])
      .map(a => {
        const match = state.activeAmenities.has(a) ? ' match' : '';
        return `<span class="amenity-badge${match}">${AMENITY_META[a].icon} ${AMENITY_META[a].label}</span>`;
      }).join('');

    return `
      <div class="stop-card" data-maps="${esc(mapsUrl)}" tabindex="0" role="link" aria-label="${esc(stop.name)}, ${distMi} miles">
        <div class="stop-header">
          <span class="stop-number">${num}</span>
          <span class="stop-icon">${icon}</span>
          <div class="stop-info">
            <div class="stop-name">${esc(stop.name)}</div>
            <div class="stop-distance">${distMi} miles ahead</div>
          </div>
          <span class="stop-arrow">›</span>
        </div>
        <div class="stop-footer">
          <div class="stop-amenities">${badges}</div>
          <a class="google-link" href="${esc(googleUrl)}" target="_blank" rel="noopener noreferrer">⭐ Ratings</a>
        </div>
      </div>`;
  }).join('');

  if (state.activeView === 'map') renderMap();
}

function showLoading() {
  document.getElementById('stops-list').innerHTML = `
    <div class="status-message">
      <div class="spinner"></div>
      <p>Searching for stops…</p>
    </div>`;
}

function showError(msg) {
  document.getElementById('stops-list').innerHTML = `
    <div class="status-message">
      <span class="status-icon">⚠️</span>
      <p>Could not load stops.</p>
      <p class="hint">${esc(msg)}</p>
      <button class="retry-btn" onclick="fetchStops()">Try Again</button>
    </div>`;
}

function esc(s) {
  return String(s)
    .replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
}

function updateHeader() {
  const locEl = document.getElementById('location-status');
  const hdgEl = document.getElementById('heading-text');
  const arrow = document.getElementById('heading-arrow');

  if (state.lat !== null) {
    locEl.textContent = `📍 ${state.lat.toFixed(4)}, ${state.lng.toFixed(4)}`;
  }

  if (state.heading !== null) {
    const cardinal = headingToCardinal(state.heading);
    const src = state.headingSource === 'compass' ? ' (compass)' : '';
    hdgEl.textContent = `Heading ${cardinal} ${Math.round(state.heading)}°${src}`;
    arrow.style.transform = `rotate(${state.heading}deg)`;
  } else {
    hdgEl.textContent = 'Showing all directions';
    arrow.style.transform = 'rotate(0deg)';
  }

  updateRangeLabel();
}

// ─── Geolocation ──────────────────────────────────────────────────────────────
function onPosition(pos) {
  state.lat = pos.coords.latitude;
  state.lng = pos.coords.longitude;

  // Track speed for time-based search (m/s → mph; ignore when effectively stopped)
  if (pos.coords.speed !== null && pos.coords.speed !== undefined) {
    const mph = pos.coords.speed * 2.23694;
    if (mph > 5) {
      state.speedHistory.push(mph);
      if (state.speedHistory.length > 8) state.speedHistory.shift();
    }
  }

  // Use GPS heading only when actually moving (speed > ~2 mph)
  if (pos.coords.heading !== null && pos.coords.heading !== undefined &&
      pos.coords.speed > 0.9) {
    state.heading      = pos.coords.heading;
    state.headingSource = 'gps';
  }

  updateHeader();
  if (shouldRefetch()) fetchStops();
}

function onPositionError(err) {
  document.getElementById('location-status').textContent = '📍 Location unavailable';
  if (err.code === 1 /* PERMISSION_DENIED */) {
    showLocationDenied();
  } else {
    document.getElementById('stops-list').innerHTML = `
      <div class="status-message">
        <span class="status-icon">⚠️</span>
        <p>Could not get your location.</p>
        <p class="hint">${esc(err.message)}</p>
        <button class="retry-btn" id="retry-location-btn">Try Again</button>
      </div>`;
    document.getElementById('retry-location-btn').addEventListener('click', startWatching);
  }
}

function showLocationPrompt() {
  document.getElementById('location-status').textContent = '📍 Location needed';
  document.getElementById('stops-list').innerHTML = `
    <div class="status-message">
      <span class="status-icon">📍</span>
      <p>Tap <strong>Enable Location Access</strong> above to get started.</p>
    </div>`;
}

function showLocationDenied() {
  document.getElementById('stops-list').innerHTML = `
    <div class="status-message">
      <span class="status-icon">🔒</span>
      <p>Location access was blocked.</p>
      <p class="hint">In Safari: Settings → Privacy & Security → Location Services → Safari → Allow While Using App.</p>
    </div>`;
}

// ─── Map ──────────────────────────────────────────────────────────────────────

// Build a DivIcon for the user's position: plain dot when no heading, arrow when moving
function makeUserIcon(heading) {
  if (heading === null) {
    return L.divIcon({
      html: '<div class="user-dot"></div>',
      className: '',
      iconSize: [18, 18],
      iconAnchor: [9, 9],
      popupAnchor: [0, -12],
    });
  }
  return L.divIcon({
    html: `<svg class="user-arrow-svg" width="32" height="32" viewBox="0 0 32 32"
              style="transform:rotate(${heading}deg);transform-origin:center">
             <circle cx="16" cy="16" r="10" fill="white" opacity="0.9"/>
             <circle cx="16" cy="16" r="8" fill="#1a3a5c"/>
             <polygon points="16,5 21,21 16,17 11,21" fill="white"/>
           </svg>`,
    className: '',
    iconSize: [32, 32],
    iconAnchor: [16, 16],
    popupAnchor: [0, -18],
  });
}

// Draw the search area on the map (sector, corridor, or circle)
function buildSearchLayer() {
  if (!state.map || state.lat === null) return;

  if (state.searchLayer) { state.searchLayer.remove(); state.searchLayer = null; }

  const rangeKm = getEffectiveRangeMiles() * 1.60934;
  const style = {
    color: '#3b82f6', fillColor: '#93c5fd',
    fillOpacity: 0.15, weight: 1.5, dashArray: '7 5', opacity: 0.55,
  };

  if (state.heading === null) {
    // Stopped — full circle radius
    state.searchLayer = L.circle([state.lat, state.lng], {
      radius: rangeKm * 1000, ...style,
    }).addTo(state.map);

  } else if (state.routeSearch) {
    const wKm = state.milesFromRoute * 1.60934;
    if (state.routePolyline && state.routePolyline.length > 1) {
      // Real road corridor — polygon buffered around OSRM route geometry
      const pts = polylineCorridorPolygon(state.routePolyline, wKm);
      state.searchLayer = L.polygon(pts, style).addTo(state.map);
    } else {
      // Fallback: straight rectangle along heading (no OSRM data yet)
      const fwd = movePoint(state.lat, state.lng, state.heading, rangeKm);
      const rA  = (state.heading + 90)  % 360;
      const lA  = (state.heading + 270) % 360;
      const pts = [
        movePoint(state.lat, state.lng, lA, wKm),
        movePoint(fwd.lat,   fwd.lng,   lA, wKm),
        movePoint(fwd.lat,   fwd.lng,   rA, wKm),
        movePoint(state.lat, state.lng, rA, wKm),
      ].map(p => [p.lat, p.lng]);
      state.searchLayer = L.polygon(pts, style).addTo(state.map);
    }

  } else {
    // Moving — sector cone ahead (±HEADING_TOLERANCE degrees)
    const pts = [[state.lat, state.lng]];
    for (let a = -HEADING_TOLERANCE; a <= HEADING_TOLERANCE; a += 4) {
      const p = movePoint(state.lat, state.lng, (state.heading + a + 360) % 360, rangeKm);
      pts.push([p.lat, p.lng]);
    }
    pts.push([state.lat, state.lng]);
    state.searchLayer = L.polygon(pts, style).addTo(state.map);
  }
}

function initMap() {
  if (state.map) return;
  if (typeof L === 'undefined') {
    document.getElementById('map-container').innerHTML =
      '<p style="padding:20px;color:#64748b;text-align:center">Map unavailable — check your connection and reload.</p>';
    return;
  }
  state.map = L.map('map-container', { zoomControl: true });
  L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {
    attribution: '© <a href="https://openstreetmap.org">OpenStreetMap</a>',
    maxZoom: 18,
  }).addTo(state.map);
}

function renderMap() {
  initMap();

  // ── Search area visualization (rendered first so markers sit on top) ──
  buildSearchLayer();

  // ── User location marker (direction arrow or plain dot) ──
  if (state.userMarker) { state.userMarker.remove(); state.userMarker = null; }
  if (state.lat !== null) {
    state.userMarker = L.marker([state.lat, state.lng], {
      icon: makeUserIcon(state.heading),
      zIndexOffset: 1000,
    }).addTo(state.map).bindPopup('📍 You are here');
  }

  // ── Stop markers ──
  state.mapMarkers.forEach(m => m.remove());
  state.mapMarkers = [];

  const filtered = getFilteredStops();
  filtered.forEach((stop, i) => {
    const num     = i + 1;
    const distMi  = kmToMiles(stop.distanceKm).toFixed(1);
    const pinIcon = L.divIcon({
      html: `<div class="map-pin">${num}</div>`,
      className: '',
      iconSize: [28, 28],
      iconAnchor: [14, 14],
      popupAnchor: [0, -16],
    });
    const marker = L.marker([stop.lat, stop.lng], { icon: pinIcon })
      .addTo(state.map)
      .bindPopup(`<strong>${esc(stop.name)}</strong><br>${distMi} mi ahead`);
    state.mapMarkers.push(marker);
  });

  // ── Fit bounds ──
  const points = [];
  if (state.lat !== null) points.push([state.lat, state.lng]);
  filtered.forEach(s => points.push([s.lat, s.lng]));
  if (points.length > 1)        state.map.fitBounds(points, { padding: [30, 30] });
  else if (points.length === 1) state.map.setView(points[0], 12);

  setTimeout(() => state.map && state.map.invalidateSize(), 100);
}

function setView(viewName) {
  state.activeView = viewName;
  const listEl  = document.getElementById('stops-list');
  const mapEl   = document.getElementById('map-container');
  const listBtn = document.getElementById('list-view-btn');
  const mapBtn  = document.getElementById('map-view-btn');

  if (viewName === 'list') {
    listEl.style.display = '';
    mapEl.style.display  = 'none';
    listBtn.classList.add('active');
    mapBtn.classList.remove('active');
  } else {
    listEl.style.display = 'none';
    mapEl.style.display  = 'block';
    listBtn.classList.remove('active');
    mapBtn.classList.add('active');
    renderMap();
  }
}

// ─── Device Compass ───────────────────────────────────────────────────────────
function setupCompassListeners() {
  if (state.compassListening) return;
  state.compassListening = true;
  window.addEventListener('deviceorientationabsolute', onOrientation, true);
  window.addEventListener('deviceorientation', onOrientation, true);
}

function onOrientation(e) {
  if (state.headingSource === 'gps') return; // GPS takes priority
  if (e.alpha === null || e.alpha === undefined) return;

  // iOS provides webkitCompassHeading (already in magnetic north degrees)
  // Android uses alpha (rotation around z-axis, convert to compass bearing)
  const h = (e.webkitCompassHeading !== undefined && e.webkitCompassHeading !== null)
    ? e.webkitCompassHeading
    : (360 - e.alpha) % 360;

  state.heading      = h;
  state.headingSource = 'compass';
  updateHeader();
}

function initEnableButton() {
  if (!navigator.geolocation) {
    document.getElementById('location-status').textContent = '📍 Not supported';
    return;
  }

  const btn = document.getElementById('enable-btn');
  const needsOrientationGesture =
    typeof DeviceOrientationEvent !== 'undefined' &&
    typeof DeviceOrientationEvent.requestPermission === 'function';

  async function onEnableClick() {
    btn.style.display = 'none';
    startWatching();
    if (needsOrientationGesture) {
      try {
        const perm = await DeviceOrientationEvent.requestPermission();
        if (perm === 'granted') setupCompassListeners();
      } catch (e) {
        console.warn('Orientation permission denied:', e);
      }
    } else {
      setupCompassListeners();
    }
  }

  btn.addEventListener('click', onEnableClick);

  if (needsOrientationGesture) {
    // iOS 13+: both permissions need a user gesture — show the button
    btn.style.display = 'inline-block';
  } else {
    // Android / desktop: compass auto-starts; check location permission state
    setupCompassListeners();
    if (navigator.permissions) {
      navigator.permissions.query({ name: 'geolocation' }).then(result => {
        if (result.state === 'granted')      { startWatching(); }
        else if (result.state === 'denied')  { showLocationDenied(); }
        else { btn.style.display = 'inline-block'; showLocationPrompt(); }
      }).catch(() => startWatching());
    } else {
      startWatching();
    }
  }
}

// ─── Event Handlers ───────────────────────────────────────────────────────────
function initEventHandlers() {
  // Amenity toggles
  document.querySelectorAll('.amenity-toggle input').forEach(cb => {
    cb.addEventListener('change', () => {
      const label   = cb.closest('.amenity-toggle');
      const amenity = label.dataset.amenity;
      if (cb.checked) { state.activeAmenities.add(amenity);    label.classList.add('active'); }
      else            { state.activeAmenities.delete(amenity); label.classList.remove('active'); }
      updateFiltersSummary();
      renderStops();
    });
  });

  // Range slider — live visual update + debounced API refetch
  const slider = document.getElementById('range-slider');
  let sliderTimer = null;
  slider.addEventListener('input', () => {
    if (state.searchMode === 'miles') state.rangeMiles  = +slider.value;
    else                              state.timeMinutes = +slider.value;
    updateRangeLabel();
    updateFiltersSummary();
    if (state.activeView === 'map' && state.map) buildSearchLayer();
    clearTimeout(sliderTimer);
    sliderTimer = setTimeout(() => { state.lastQueryTime = null; fetchStops(); }, 1500);
  });

  // Search mode toggle
  document.getElementById('miles-mode-btn').addEventListener('click', () => {
    setSearchMode('miles'); updateFiltersSummary();
  });
  document.getElementById('time-mode-btn').addEventListener('click', () => {
    setSearchMode('time'); updateFiltersSummary();
  });

  // Refresh button
  document.getElementById('refresh-btn').addEventListener('click', () => {
    state.lastQueryTime = null;
    fetchStops();
  });

  // View toggle
  document.getElementById('list-view-btn').addEventListener('click', () => setView('list'));
  document.getElementById('map-view-btn').addEventListener('click',  () => setView('map'));

  // Route search toggle
  const routeToggle   = document.getElementById('route-search-toggle');
  const routeWidthRow = document.getElementById('route-width-row');
  routeToggle.addEventListener('change', () => {
    state.routeSearch = routeToggle.checked;
    if (!state.routeSearch) state.routePolyline = null;
    routeWidthRow.style.display = state.routeSearch ? 'block' : 'none';
    updateFiltersSummary();
    state.lastQueryTime = null;
    fetchStops();
    if (state.activeView === 'map') renderMap();
  });

  // Route width slider — debounced
  const routeWidthSlider = document.getElementById('route-width-slider');
  const routeWidthVal    = document.getElementById('route-width-val');
  let routeWidthTimer = null;
  routeWidthSlider.addEventListener('input', () => {
    state.milesFromRoute = +routeWidthSlider.value;
    routeWidthVal.textContent = state.milesFromRoute;
    updateFiltersSummary();
    if (state.activeView === 'map' && state.map) buildSearchLayer();
    clearTimeout(routeWidthTimer);
    routeWidthTimer = setTimeout(() => { state.lastQueryTime = null; fetchStops(); }, 1500);
  });

  // Stop card tap → Apple Maps directions (delegated)
  document.getElementById('stops-list').addEventListener('click', e => {
    if (e.target.closest('.google-link')) return; // let the <a> handle itself
    const card = e.target.closest('.stop-card');
    if (card?.dataset.maps) window.open(card.dataset.maps, '_blank');
  });
  // Keyboard accessibility for stop cards
  document.getElementById('stops-list').addEventListener('keydown', e => {
    if (e.key === 'Enter' || e.key === ' ') {
      const card = e.target.closest('.stop-card');
      if (card?.dataset.maps) { e.preventDefault(); window.open(card.dataset.maps, '_blank'); }
    }
  });

  // Collapsible filter panel
  const filterToggle = document.getElementById('filters-toggle');
  const filterBody   = document.getElementById('filters-body');
  const filterChevron = document.getElementById('filters-chevron');
  filterToggle.addEventListener('click', () => {
    const expanded = filterToggle.getAttribute('aria-expanded') === 'true';
    filterToggle.setAttribute('aria-expanded', String(!expanded));
    filterBody.classList.toggle('expanded', !expanded);
    filterChevron.style.transform = !expanded ? 'rotate(180deg)' : '';
  });

  updateFiltersSummary();
}

// ─── Service Worker ───────────────────────────────────────────────────────────
function registerSW() {
  if ('serviceWorker' in navigator) {
    navigator.serviceWorker.register('sw.js').catch(e => console.warn('SW:', e));
  }
}

// ─── Geolocation ──────────────────────────────────────────────────────────────
function startWatching() {
  navigator.geolocation.watchPosition(onPosition, onPositionError, {
    enableHighAccuracy: true,
    maximumAge: 10000,
    timeout: 20000,
  });
}

// ─── Init ─────────────────────────────────────────────────────────────────────
function init() {
  registerSW();
  initEventHandlers();
  initEnableButton();
  updateRangeLabel();
}

init();
