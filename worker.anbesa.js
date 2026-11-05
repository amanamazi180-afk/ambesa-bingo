// worker.anbesa.js - NEW entry file. It runs your old Worker (now named worker.core.js) and adds the Aviator game on top of it.
// Nothing inside the old Worker is changed.
import core, { GameHub, verifyInit } from './worker.core.js';
import { avRoute } from './aviator-worker.js';
export { GameHub }; // the game server class must be exported from the entry file
const J = (o, s = 200) => new Response(JSON.stringify(o), { status: s, headers: { 'content-type': 'application/json' } });
export default {
  async fetch(req, env, ctx) {
    const url = new URL(req.url);
    if (!url.pathname.startsWith('/api/av/')) return core.fetch(req, env, ctx); // everything else = your normal bingo Worker
    const cors = { 'access-control-allow-origin': env.ALLOW_ORIGIN || '*', 'access-control-allow-headers': 'content-type,x-init-data,x-admin-key', 'access-control-allow-methods': 'GET,POST,OPTIONS' };
    if (req.method === 'OPTIONS') return new Response(null, { headers: cors });
    let res;
    try {
      const tu = await verifyInit(req.headers.get('x-init-data'), env.BOT_TOKEN);
      if (!tu) res = J({ error: 'unauthorized' }, 401);
      else {
        const u = await env.DB.prepare('SELECT * FROM users WHERE id=?').bind(tu.id).first();
        if (!u || !u.phone) res = J({ error: 'not_registered' }, 403);
        else if (await env.DB.prepare('SELECT 1 x FROM bans WHERE id=?').bind(tu.id).first().catch(() => null)) res = J({ error: 'banned' }, 403);
        else res = await avRoute(req, env, url.pathname, u, req.method === 'POST' ? await req.json().catch(() => ({})) : {});
      }
    } catch (e) { res = J({ error: 'server_error', detail: String(e.message || e) }, 500); }
    for (const [k, v] of Object.entries(cors)) res.headers.set(k, v);
    return res;
  }
};
