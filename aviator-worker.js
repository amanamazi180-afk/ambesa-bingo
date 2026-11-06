// aviator-worker.js - Aviator game server for the Ambesa Worker. Uses the SAME wallet (users.balance, in cents) as the bingo.
// Needs only 2 edits in worker.anbesa.js (see the instructions). Tables are created automatically. Deposits use the bot's existing system.
const C = { edge: 0.04, max: 4000, betMs: 6000, coolMs: 4000, minBet: 4, maxBet: 4000, maxWinC: 10000000 }; // max single win = 100,000 birr
const J = (d, s = 200) => new Response(JSON.stringify(d), { status: s, headers: { 'content-type': 'application/json' } });
const r2 = n => Math.floor(n * 100 + 1e-9) / 100;
const mult = ms => { const t = ms / 1000; return Math.max(1, r2(Math.exp(0.1 * t * (1 + 0.012 * t)))); }; // same curve as the page
const msOf = m => 1000 * (-0.1 + Math.sqrt(0.01 + 0.0048 * Math.log(m))) / 0.0024;                          // time needed to reach multiplier m
function crashPoint() { const u = new Uint32Array(1); crypto.getRandomValues(u); return Math.min(C.max, Math.max(1, r2((1 - C.edge) / (1 - u[0] / 4294967296)))); } // 4% house edge, picked on the server only
let ready = false, rc = { t: 0, r: null };
async function init(db) {
  if (ready) return;
  await db.batch([
    db.prepare('CREATE TABLE IF NOT EXISTS av_rounds(id INTEGER PRIMARY KEY,crash REAL NOT NULL,start_ms INTEGER NOT NULL,end_ms INTEGER NOT NULL)'),
    db.prepare("CREATE TABLE IF NOT EXISTS av_bets(id INTEGER PRIMARY KEY AUTOINCREMENT,round_id INTEGER NOT NULL,user_id INTEGER NOT NULL,slot INTEGER NOT NULL,amount INTEGER NOT NULL,auto_at REAL,status TEXT NOT NULL DEFAULT 'open',payout INTEGER,UNIQUE(round_id,user_id,slot))"),
    db.prepare('CREATE INDEX IF NOT EXISTS av_b_user ON av_bets(user_id,status)')]);
  ready = true;
}
async function round(db, now) { // the current round; a new one starts after the last one finished + cooldown
  if (rc.r && now - rc.t < 250 && now < rc.r.end_ms + C.coolMs) return rc.r;
  let r = await db.prepare('SELECT * FROM av_rounds ORDER BY id DESC LIMIT 1').first();
  if (!r || now >= r.end_ms + C.coolMs) {
    const cp = crashPoint(), st = now + C.betMs;
    await db.prepare('INSERT OR IGNORE INTO av_rounds(id,crash,start_ms,end_ms) VALUES(?,?,?,?)').bind((r ? r.id : 0) + 1, cp, st, Math.ceil(st + msOf(cp))).run();
    r = await db.prepare('SELECT * FROM av_rounds ORDER BY id DESC LIMIT 1').first();
  }
  rc = { t: now, r }; return r;
}
async function pay(db, uid, b, m) { // pays a winning bet exactly once (status must still be 'open')
  const win = Math.min(Math.floor(b.amount * m), C.maxWinC);
  const ok = (await db.prepare("UPDATE av_bets SET status='won',payout=? WHERE id=? AND status='open'").bind(win, b.id).run()).meta.changes === 1;
  if (ok) await db.prepare('UPDATE users SET balance=balance+? WHERE id=?').bind(win, uid).run();
  return ok ? win : 0;
}
async function settle(db, uid, now) { // this player's open bets: auto cash-out reached -> pay, round over -> lost
  const rows = (await db.prepare("SELECT b.id,b.amount,b.auto_at,r.crash,r.start_ms,r.end_ms FROM av_bets b JOIN av_rounds r ON r.id=b.round_id WHERE b.user_id=? AND b.status='open' AND r.start_ms<=?").bind(uid, now).all()).results;
  for (const b of rows) {
    if (b.auto_at && b.auto_at <= b.crash && now >= b.start_ms + msOf(b.auto_at)) await pay(db, uid, b, b.auto_at);
    else if (now >= b.end_ms) await db.prepare("UPDATE av_bets SET status='lost' WHERE id=? AND status='open'").bind(b.id).run();
  }
}
export async function avRoute(req, env, p, u, b) { // u = the logged-in, registered, not-banned player (already checked by the Worker)
  const db = env.DB, now = Date.now(), B = c => c / 100, slot = b.slot === 2 ? 2 : 1;
  await init(db);
  const bal = async () => (await db.prepare('SELECT balance FROM users WHERE id=?').bind(u.id).first()).balance;
  if (p === '/api/av/state') {
    await settle(db, u.id, now); const r = await round(db, now);
    const phase = now < r.start_ms ? 'betting' : now < r.end_ms ? 'flying' : 'crashed';
    const hist = new URL(req.url).searchParams.get('h') ? (await db.prepare('SELECT crash FROM av_rounds WHERE end_ms<=? ORDER BY id DESC LIMIT 40').bind(now).all()).results.map(x => x.crash) : [];
    const mine = (await db.prepare('SELECT slot,amount,status,payout FROM av_bets WHERE round_id=? AND user_id=?').bind(r.id, u.id).all()).results.map(x => ({ slot: x.slot, amount: B(x.amount), status: x.status, payout: B(x.payout || 0) }));
    return J({ round: r.id, phase, now, start_ms: r.start_ms, crash: phase === 'crashed' ? r.crash : null, history: hist, mine, balance: B(await bal()) });
  }
  if (p === '/api/av/bet') { // {slot, amount (birr), auto}
    const a = Math.round(Number(b.amount) * 100) / 100, auto = Number(b.auto) > 1 ? Math.min(C.max, Math.max(1.01, Number(b.auto))) : null;
    if (!(a >= C.minBet && a <= C.maxBet)) return J({ error: `Bet ${C.minBet} - ${C.maxBet} ETB` }, 400);
    const r = await round(db, now); if (now >= r.start_ms) return J({ error: 'Betting closed, wait for the next round' }, 400);
    const c = Math.round(a * 100);
    if ((await db.prepare('UPDATE users SET balance=balance-?1 WHERE id=?2 AND balance>=?1').bind(c, u.id).run()).meta.changes !== 1) return J({ error: 'Not enough balance' }, 400);
    try { await db.prepare('INSERT INTO av_bets(round_id,user_id,slot,amount,auto_at) VALUES(?,?,?,?,?)').bind(r.id, u.id, slot, c, auto).run(); }
    catch (e) { await db.prepare('UPDATE users SET balance=balance+? WHERE id=?').bind(c, u.id).run(); return J({ error: 'You already bet on this panel' }, 400); }
    return J({ ok: true, balance: B(await bal()) });
  }
  if (p === '/api/av/cancel') { // take the bet back while betting is still open
    const r = await round(db, now); if (now >= r.start_ms) return J({ error: 'Too late' }, 400);
    const x = await db.prepare("SELECT id,amount FROM av_bets WHERE round_id=? AND user_id=? AND slot=? AND status='open'").bind(r.id, u.id, slot).first();
    if (x && (await db.prepare("UPDATE av_bets SET status='cancelled' WHERE id=? AND status='open'").bind(x.id).run()).meta.changes === 1) await db.prepare('UPDATE users SET balance=balance+? WHERE id=?').bind(x.amount, u.id).run();
    return J({ ok: true, balance: B(await bal()) });
  }
  if (p === '/api/av/cashout') {
    await settle(db, u.id, now);
    const x = await db.prepare("SELECT b.id,b.amount,r.crash,r.start_ms,r.end_ms FROM av_bets b JOIN av_rounds r ON r.id=b.round_id WHERE b.user_id=? AND b.slot=? AND b.status='open' ORDER BY b.id DESC LIMIT 1").bind(u.id, slot).first();
    if (!x || now < x.start_ms || now >= x.end_ms) return J({ error: 'Too late' }, 400);
    const win = await pay(db, u.id, x, Math.min(mult(now - x.start_ms), x.crash));
    return J({ ok: true, payout: B(win), balance: B(await bal()) });
  }
  return J({ error: 'not_found' }, 404);
}
