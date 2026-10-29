/* fast repeat loads: voices + lion are cached on the phone; page is always checked online first */
const V="anbesa-v1";
self.addEventListener("install",e=>self.skipWaiting());
self.addEventListener("activate",e=>e.waitUntil(caches.keys().then(k=>Promise.all(k.filter(x=>x!==V).map(x=>caches.delete(x)))).then(()=>self.clients.claim())));
self.addEventListener("fetch",e=>{
  const r=e.request,u=new URL(r.url);
  if(r.method!=="GET"||u.origin!==location.origin)return;           /* never touch the game server calls */
  if(/\.(m4a|webp|png|jpg|svg)$/.test(u.pathname)){                /* cache first: instant */
    e.respondWith(caches.open(V).then(c=>c.match(r,{ignoreSearch:true}).then(m=>m||fetch(r).then(n=>{if(n.ok)c.put(r,n.clone());return n}))));
    return
  }
  e.respondWith(fetch(r).then(n=>{if(n.ok){const k=n.clone();caches.open(V).then(c=>c.put(r,k))}return n}).catch(()=>caches.match(r)));  /* page: online first, offline fallback */
});
