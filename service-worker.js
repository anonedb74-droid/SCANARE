// Scanare documente — rețeaua întâi, apoi cache (merge și fără semnal)
const CACHE_NAME = 'scanare-cache-v2';
const FISIERE = ['./', './index.html', './manifest.json', './icon-192.png', './icon-512.png'];
self.addEventListener('install', e => { e.waitUntil(caches.open(CACHE_NAME).then(c => c.addAll(FISIERE))); self.skipWaiting(); });
self.addEventListener('activate', e => {
  e.waitUntil(caches.keys().then(k => Promise.all(k.filter(n => n !== CACHE_NAME).map(n => caches.delete(n)))));
  self.clients.claim();
});
self.addEventListener('fetch', e => {
  const r = e.request;
  if (r.method !== 'GET') return;
  const url = new URL(r.url);
  const fonturi = url.hostname.includes('fonts.g');
  if (url.origin !== location.origin && !fonturi) return;
  e.respondWith(
    fetch(r).then(res => {
      if (res.ok || res.type === 'opaque') { const copie = res.clone(); caches.open(CACHE_NAME).then(c => c.put(r, copie)); }
      return res;
    }).catch(() => caches.match(r).then(m => m || caches.match('./index.html')))
  );
});
