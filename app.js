'use strict';

// ─── Constants ────────────────────────────────────────────────────────────────
const OVERPASS_URL = 'https://overpass-api.de/api/interpreter';
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
  isLoading: false,
  compassListening: false,
  map: null,
  mapMarkers: [],
  userMarker: null,
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

// ─── Overpass API ─────────────────────────────────────────────────────────────
async function fetchStops() {
  if (!state.lat || !state.lng || state.isLoading) return;

  const rangeKm = state.rangeMiles * 1.60934;
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
  showLoading();

  try {
    const resp = await fetch(OVERPASS_URL, {
      method: 'POST',
      headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
      body: `data=${encodeURIComponent(query)}`,
    });
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
      .sort((a, b) => a.distanceKm - b.distanceKm);

    state.lastQueryLat  = state.lat;
    state.lastQueryLng  = state.lng;
    state.lastQueryTime = Date.now();

    renderStops();
  } catch (err) {
    console.error('Overpass error:', err);
    showError(err.message);
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
  return false;
}

// ─── UI ───────────────────────────────────────────────────────────────────────
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
    const num     = i + 1;
    const distMi  = kmToMiles(stop.distanceKm).toFixed(1);
    const icon    = TYPE_ICON[stop.type] || '📍';
    const mapsUrl = `https://maps.apple.com/?daddr=${stop.lat},${stop.lng}&dirflg=d`;

    const badges = stop.amenities
      .filter(a => AMENITY_META[a])
      .map(a => {
        const match = state.activeAmenities.has(a) ? ' match' : '';
        return `<span class="amenity-badge${match}">${AMENITY_META[a].icon} ${AMENITY_META[a].label}</span>`;
      }).join('');

    return `
      <a class="stop-card" href="${mapsUrl}" target="_blank" rel="noopener noreferrer">
        <div class="stop-header">
          <span class="stop-number">${num}</span>
          <span class="stop-icon">${icon}</span>
          <div class="stop-info">
            <div class="stop-name">${esc(stop.name)}</div>
            <div class="stop-distance">${distMi} miles ahead</div>
          </div>
          <span class="stop-arrow">›</span>
        </div>
        <div class="stop-amenities">${badges}</div>
      </a>`;
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
}

// ─── Geolocation ──────────────────────────────────────────────────────────────
function onPosition(pos) {
  state.lat = pos.coords.latitude;
  state.lng = pos.coords.longitude;

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
function initMap() {
  if (state.map) return;
  state.map = L.map('map-container', { zoomControl: true });
  L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {
    attribution: '© <a href="https://openstreetmap.org">OpenStreetMap</a>',
    maxZoom: 18,
  }).addTo(state.map);
}

function renderMap() {
  initMap();

  // User location marker
  if (state.lat !== null) {
    if (state.userMarker) {
      state.userMarker.setLatLng([state.lat, state.lng]);
    } else {
      state.userMarker = L.circleMarker([state.lat, state.lng], {
        radius: 9, fillColor: '#1a3a5c', color: '#ffffff', weight: 2.5, fillOpacity: 1,
      }).addTo(state.map).bindPopup('📍 You are here');
    }
  }

  // Clear old stop markers
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

  // Fit map to show user + all stops
  const points = [];
  if (state.lat !== null) points.push([state.lat, state.lng]);
  filtered.forEach(s => points.push([s.lat, s.lng]));
  if (points.length > 1)     state.map.fitBounds(points, { padding: [30, 30] });
  else if (points.length === 1) state.map.setView(points[0], 12);

  state.map.invalidateSize();
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
    mapEl.style.display  = '';
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
      renderStops();
    });
  });

  // Range slider
  const slider   = document.getElementById('range-slider');
  const rangeVal = document.getElementById('range-value');
  slider.addEventListener('input',  () => { state.rangeMiles = +slider.value; rangeVal.textContent = slider.value; });
  slider.addEventListener('change', () => { state.lastQueryTime = null; fetchStops(); });

  // Refresh button
  document.getElementById('refresh-btn').addEventListener('click', () => {
    state.lastQueryTime = null;
    fetchStops();
  });

  // View toggle
  document.getElementById('list-view-btn').addEventListener('click', () => setView('list'));
  document.getElementById('map-view-btn').addEventListener('click',  () => setView('map'));
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
}

init();
