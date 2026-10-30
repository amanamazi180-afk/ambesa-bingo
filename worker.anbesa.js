// Anbesa Bingo server (made from Aman by patch-worker.js) — Cloudflare Worker + D1 database + Durable Object (GameHub) that runs the live game.
// Money is stored in cents (birr x 100). Variables to set in Cloudflare:
//   BOT_TOKEN, ADMIN_TG_ID, SMS_SECRET, TG_SECRET, ADMIN_KEY, VERIFYET_KEY (secrets) · GAME_URL, ALLOW_ORIGIN, STAKE (plain variables)
//   Optional: ALLOW_MANUAL_DEPOSIT (1 = admin may approve deposits by hand; default LOCKED), BOT_USERNAME, DAILY_BONUS, ADMIN_URL, PROMO_PHOTO, VERIFYET_MIN, VERIFYET_AUTO_MAX, FIRST_DEP_MAX, VET_DAILY_MAX, SMS_SENDERS
// wrangler.json needs the HUB binding + migration for GameHub (unchanged).
// NO WELCOME BONUS: a new player gets nothing when registering, only the message "እንኳን ደስ አሎት ተመዝግበዋል" with the play buttons.
// DEPOSIT BANKS (bot + game wallet): CBE, Telebirr, M-Pesa, E-birr (the admin edits numbers, names and pictures in Admin > Accounts).
// WITHDRAW BANKS: CBE, Dashen, Oromia, Awash, BOA, M-Pesa, Telebirr, E-birr (WD_BANKS below).
// WIN RULES: a full line (row, column or diagonal) OR the 4 CORNERS of the cartela wins (see hasBingo below).
// DEPOSIT GUARD: a deposit is credited AUTOMATICALLY only by (1) a matching bank SMS forwarded to POST /sms (same transaction number AND amount, sender must be a bank)
//   or (2) verify.et (Telebirr / M-Pesa: real receipt + paid to OUR account + same amount + not older than 72 hours). A deposit is HELD for the admin when verify.et disagrees,
//   the amount is above VERIFYET_AUTO_MAX (default 1000) for the verify.et way, it is a FIRST deposit above FIRST_DEP_MAX (default 1000), the player has 2+ rejected deposits,
//   more than VET_DAILY_MAX (default 3000) was credited by verify.et alone in 24 h, or there are more than 3 pending requests. The "✅ አጽድቅ" button is shown ONLY for a HELD deposit
//   (unless ALLOW_MANUAL_DEPOSIT=1). Every automatic credit tells the admins "Approved by verify.et / SMS match / SMS + verify.et".
// SECRET BONUS (Admin > Bonus), WEEKLY BONUS (Admin > Weekly), AUTO-TAKE (Admin > AutoTake), ACCOUNTS (Admin > Accounts), DEPOSITS LIST (Admin > Overview) work as before.
// SPEED (this version): tables are created only once ever (marker schema_v2) + indexes; admin pages read the database in parallel; the admin list is cached 30 s;
//   a pick needs 2 database round trips (the secret-bonus setting is kept in the GameHub memory); the round-end screen no longer waits for the winners' Telegram messages.
// BROADCAST: /broadcast text sends to ALL registered players from ONE command, in the background (about 25 messages per second = Telegram's safe speed). /more = progress, /stopbroadcast = stop.
//   It runs in a separate GameHub instance named "bc" (Durable Object alarms), so it never slows the game.
import { DurableObject } from 'cloudflare:workers';
const LOBBY_MS = 40000, CALL_MS = 4000, REST_MS = 8000, CUT = 0.8, MAXC = 2, TOTAL = 400, MIN_DEP = 30, MIN_WD = 50, MIN_TR = 10;
const C = x => Math.round(Number(x) * 100), B = c => c / 100;
const welcomeC = env => 0; // the welcome gift is switched off for good: nobody gets money for joining
const bonusC = env => C(env.DAILY_BONUS ?? 0), // daily bonus is off unless DAILY_BONUS is set
   bonusPeriod = now => Math.floor((now - 5 * 36e5) / 864e5); // new period starts 08:00 Ethiopia time (05:00 UTC)
const refreshBonusStmt = (env, id, now) => env.DB.prepare('UPDATE users SET bonus_c=?1,bonus_period=?2 WHERE id=?3 AND (bonus_period<?2 OR (?1=0 AND bonus_c<>0))').bind(bonusC(env), bonusPeriod(now), id); // resets to the daily amount (0 = off), never added on top
const refreshBonus = (env, id, now) => refreshBonusStmt(env, id, now).run();
const rnd32 = () => crypto.getRandomValues(new Uint32Array(1))[0];
const sleep = ms => new Promise(r => setTimeout(r, ms));
const J = (o, s = 200) => new Response(JSON.stringify(o), { status: s, headers: { 'content-type': 'application/json' } });

/* ---------- pure game logic (same card generator as the app) ---------- */
export function mulberry(a) { return () => { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296 } }
export function numberOrder(seed) { const r = mulberry(seed), a = Array.from({ length: 75 }, (_, i) => i + 1); for (let i = 74; i > 0; i--) { const j = Math.floor(r() * (i + 1));[a[i], a[j]] = [a[j], a[i]] } return a }
export function makeCard(no) {
  let s = no * 7919 + 13; const r = () => { s = (s * 1664525 + 1013904223) % 4294967296; return s / 4294967296 }, cols = [];
  for (let c = 0; c < 5; c++) { const pool = Array.from({ length: 15 }, (_, i) => c * 15 + i + 1), out = []; for (let i = 0; i < 5; i++) out.push(pool.splice(Math.floor(r() * pool.length), 1)[0]); cols.push(out) }
  cols[2][2] = 0; return cols;
}
export function hasBingo(card, marked) {
  const m = (c, r) => { const v = card[c][r]; return v === 0 || marked.has(v) }, n = [0, 1, 2, 3, 4];
  if (m(0, 0) && m(4, 0) && m(0, 4) && m(4, 4)) return true; // 4 CORNERS win
  for (let i = 0; i < 5; i++) if (n.every(j => m(j, i)) || n.every(j => m(i, j))) return true;
  return n.every(i => m(i, i)) || n.every(i => m(i, 4 - i));
}
// earliest call number at which any picked cartela completes; every cartela completing on that call wins (ties split)
export function findWinners(order, picks, k) {
  const cards = picks.map(p => makeCard(p.cartela)), marked = new Set();
  for (let kk = 1; kk <= k; kk++) { marked.add(order[kk - 1]); const w = picks.filter((_, i) => hasBingo(cards[i], marked)); if (w.length) return { k: kk, picks: w } }
  return null;
}

/* ---------- deposit SMS reading: Telebirr, Dashen, BOA, CBE ---------- */
const toNum = s => Number(String(s).replace(/,/g, ''));
const FT = s => String(s).toUpperCase().slice(0, 12); // bank references (FT…) are keyed by their first 12 characters, so a receipt link and a feedback link of the same payment give the same id
// Reads a "money received" SMS. Returns { bank, amount_c, txid } or null (money-sent messages and anything else are ignored).
//  Telebirr: "… 300.00 ብር በ 10/10/2026 11:14:57 ተቀብለዋል። የሂሳብ እንቅስቃሴ ቁጥርዎ DJA8MMWD4O ነዉ።"
//  BOA:      "… was credited with ETB 50.00 by NAME … Receipt: https://cs.bankofabyssinia.com/slip/?trx=FT2627850CY910104"
//  Dashen 1: "You have received ETB 6,000.00 from NAME on 2026-09-29 at 09:48:09 with transaction reference: 112WDTS262720002."
//  Dashen 2: "… credited with ETB 40.00 … on 05/10/2026 at 11:24:14 PM. Your current balance is ETB 303.20." (id built from date + time + balance)
//  CBE:      "… Credited with ETB … Ref No FT26283XXXXX …" (format not tested with a real sample yet)
//  M-Pesa / E-birr: no reader yet; those deposits are approved by verify.et (M-Pesa) or the admin.
export function parseBank(t) {
  t = String(t || '');
  let a, i, m;
  if (/ተቀብለዋል/.test(t)) { // Telebirr (Amharic)
    a = t.match(/([\d,]+(?:\.\d+)?)\s*ብር\s*በ\s*\d{2}\/\d{2}\/\d{4}/); i = t.match(/ቁጥርዎ\s+([A-Z0-9]{8,14})/i);
    if (a && i) return { bank: 'telebirr', amount_c: C(toNum(a[1])), txid: i[1].toUpperCase() };
  }
  a = t.match(/you\s+have\s+received\s+ETB\s*([\d,]+(?:\.\d+)?)/i); i = t.match(/transaction\s*(?:number|id|no\.?)\s*(?:is|:)?\s*([A-Z0-9]{8,14})/i);
  if (a && i) return { bank: 'telebirr', amount_c: C(toNum(a[1])), txid: i[1].toUpperCase() }; // Telebirr (English)
  a = t.match(/received\s+ETB\s*([\d,]+(?:\.\d+)?)/i); i = t.match(/transaction\s*reference\s*[:.]?\s*([A-Z0-9]{8,24})/i);
  if (a && i) return { bank: 'dashen', amount_c: C(toNum(a[1])), txid: i[1].toUpperCase() }; // Dashen "You have received ETB … with transaction reference: …"
  a = t.match(/credited\s+with\s+ETB\s*([\d,]+(?:\.\d+)?)/i); // Dashen, BOA and CBE all say "credited with ETB …"
  if (!a) return null;
  const amount_c = C(toNum(a[1]));
  m = t.match(/slip\/\s*\?trx=\s*([A-Z0-9]{8,24})/i) || t.match(/cs\/\s*\?trx=\s*[A-Z]?(FT[A-Z0-9]{8,22})/i); // BOA
  if (m) return { bank: 'boa', amount_c, txid: FT(m[1]) };
  m = t.match(/ref(?:erence)?\s*(?:no\.?|number)?\s*[:.]?\s*(FT[A-Z0-9]{8,22})/i) || t.match(/[?&]id=(FT[A-Z0-9]{8,22})/i); // CBE
  if (m) return { bank: 'cbe', amount_c, txid: FT(m[1]) };
  const dt = t.match(/(\d{2})\/(\d{2})\/(\d{4})\s+at\s+(\d{1,2}):(\d{2}):(\d{2})\s*([AP])M/i); // Dashen
  if (!dt) return null;
  const bal = t.match(/balance\s+is\s+ETB\s*([\d,]+(?:\.\d+)?)/i);
  return { bank: 'dashen', amount_c, txid: ('DSH' + dt[1] + dt[2] + dt[3] + dt[4].padStart(2, '0') + dt[5] + dt[6] + dt[7] + (bal ? C(toNum(bal[1])) : 0)).toUpperCase() };
}
export const parseSms = parseBank; // the SMS-forwarder route uses the same reader
// reads the payment message a player pastes in the bot: a known bank SMS gives bank + amount + transaction number; anything else just looks for a transaction number
export function parsePaste(t) {
  t = String(t || '');
  const b = parseBank(t); if (b) return b;
  const lab = t.match(/(?:transaction\s*(?:number|id|no\.?)|ref(?:erence)?(?:\s*(?:no\.?|number|id))?|receipt\s*(?:no\.?|number)|ቁጥርዎ|ቁጥር)\s*(?:is|:|-)?\s*([A-Z0-9]{8,20})\b/i);
  if (lab && /\d/.test(lab[1]) && /[A-Z]/i.test(lab[1])) return { txid: lab[1].toUpperCase() };
  const all = (t.toUpperCase().match(/\b[A-Z0-9]{8,20}\b/g) || []).filter(x => /\d/.test(x) && /[A-Z]/.test(x));
  return all.length ? { txid: all[0] } : null;
}
export function normPhone(p) { p = String(p || '').replace(/[\s-]/g, ''); if (/^\+?251[79]\d{8}$/.test(p)) p = '0' + p.replace(/^\+?251/, ''); return /^0[79]\d{8}$/.test(p) ? p : null }

/* ---------- Telegram helpers ---------- */
async function hmac(key, msg) { const k = await crypto.subtle.importKey('raw', key, { name: 'HMAC', hash: 'SHA-256' }, false, ['sign']); return new Uint8Array(await crypto.subtle.sign('HMAC', k, msg)) }
export async function verifyInit(initData, token, maxAge = 86400) {
  const p = new URLSearchParams(initData || ''), hash = p.get('hash'); if (!hash) return null; p.delete('hash');
  const str = [...p.entries()].sort(([a], [b]) => a < b ? -1 : 1).map(([k, v]) => k + '=' + v).join('\n'), enc = new TextEncoder();
  const sig = await hmac(await hmac(enc.encode('WebAppData'), enc.encode(token)), enc.encode(str));
  if ([...sig].map(b => b.toString(16).padStart(2, '0')).join('') !== hash) return null;
  if (Date.now() / 1000 - Number(p.get('auth_date') || 0) > maxAge) return null;
  try { return JSON.parse(p.get('user')) } catch (e) { return null }
}
const tg = (env, method, body) => fetch(`https://api.telegram.org/bot${env.BOT_TOKEN}/${method}`, { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify(body) }).catch(() => { });
// Owners come from the ADMIN_TG_ID secret (can hold several ids: 111,222). Extra admins live in the database and are managed with /addadmin /removeadmin /admins.
const owners = env => String(env.ADMIN_TG_ID || '').split(',').map(s => s.trim()).filter(Boolean);
let admCache = { t: 0, l: [] }; // the database admin list is cached for 30 seconds (say() asks for it on every message that has a play button)
const dbAdmins = async env => { if (Date.now() - admCache.t < 30000) return admCache.l; try { await ensureTables(env); const l = (await env.DB.prepare('SELECT id FROM admins').all()).results.map(r => String(r.id)); admCache = { t: Date.now(), l }; return l } catch (e) { return admCache.l } };
const admins = async env => [...new Set([...owners(env), ...await dbAdmins(env)])];
const isOwner = (env, id) => owners(env).includes(String(id));
const isAdmin = async (env, id) => isOwner(env, id) || (await dbAdmins(env)).includes(String(id));
const adminUrl = env => env.ADMIN_URL || ((env.GAME_URL || '').replace(/\/?$/, '/') + 'admin.html');
const say = async (env, chat, text, kb) => { // the Admin button is added only for an admin's own chat
  if (kb && kb[0] && kb[0][0] && kb[0][0].web_app && await isAdmin(env, chat)) kb = [...kb, [{ text: 'Admin 🛠', web_app: { url: adminUrl(env) } }]];
  return tg(env, 'sendMessage', { chat_id: chat, text, reply_markup: kb ? { inline_keyboard: kb } : undefined });
};
const playKb = env => [[{ text: '🎮 ተጫወት', web_app: { url: env.GAME_URL } }]];

/* ---------- bot menu (inline buttons, like DIL BINGO), bottom keyboard and Amharic texts ---------- */
const SUPPORT = '@Kidwda';
const BTN = { play: '🎮 ጨዋታ ተጫወት', dep: '💰 ገንዘብ አስገባ', bal: '💳 ቀሪ ሂሳብ', sup: '🆘 እርዳታ' }; // old bottom-keyboard texts, still understood
const BOT = { play: '🎮 ጨዋታ ተጫወት', dep: '💰 ገንዘብ አስገባ', bal: '💲 ቀሪ ሂሳብ' }; // the permanent keyboard under the chat box (Amharic)
const LEG = { '🎮 Play Games': BOT.play, '💰 Deposit': BOT.dep, '💲 Check Balance': BOT.bal }; // the OLD English keyboard texts: players who still have that keyboard keep working
const BOTTOM_KB = { keyboard: [[{ text: BOT.play }, { text: BOT.dep }], [{ text: BOT.bal }]], resize_keyboard: true, is_persistent: true };
const isBtn = t => Object.values(BTN).includes(t) || Object.values(BOT).includes(t) || t in LEG;
const sendTo = (env, chat, text, markup) => tg(env, 'sendMessage', { chat_id: chat, text, reply_markup: markup });
const sendBottom = async (env, chat, text) => { try { await env.DB.prepare('INSERT OR IGNORE INTO kb_sent(uid) VALUES(?)').bind(chat).run() } catch (e) { } return sendTo(env, chat, text, BOTTOM_KB) }; // shows (or refreshes) the bottom keyboard and remembers that this player has it
const SHARE_KB = { keyboard: [[{ text: '📱 ስልክ ቁጥሬን አጋራ', request_contact: true }]], resize_keyboard: true, one_time_keyboard: true };
const menuKb = env => [
  [{ text: 'ተጫወት 🎮', web_app: { url: env.GAME_URL } }],
  [{ text: 'ቀሪ ሂሳብ 💵', callback_data: 'm:bal' }, { text: 'ገንዘብ አስገባ 💰', callback_data: 'm:dep' }],
  [{ text: 'እርዳታ 🆘', url: 'https://t.me/' + SUPPORT.slice(1) }, { text: 'መመሪያ 📖', callback_data: 'm:ins' }],
  [{ text: 'አስተላልፍ 🎁', callback_data: 'm:tr' }, { text: 'አውጣ 🤑', callback_data: 'm:wd' }],
  [{ text: 'ጋብዝ 🔗', callback_data: 'm:inv' }]];
const sendMenu = (env, chat, text) => say(env, chat, text, menuKb(env));
const askContact = (env, uid) => sendTo(env, uid, '👋 እንኳን ወደ አንበሳ Bingo በደህና መጡ!\n\nለመመዝገብ ከታች ያለውን «📱 ስልክ ቁጥሬን አጋራ» ቁልፍ ይጫኑ።', SHARE_KB);
const instructionText = `📖 እንዴት ይጫወታሉ?\n\n1️⃣ «ገንዘብ አስገባ» ን ተጭነው ገንዘብ ያስገቡ (ቢያንስ ${MIN_DEP} ብር)።\n2️⃣ «ተጫወት» ን ተጭነው ጨዋታውን ይክፈቱ።\n3️⃣ ከ1 እስከ ${TOTAL} ካርቴላ ይምረጡ — እስከ ${MAXC} ካርቴላ መያዝ ይቻላል።\n4️⃣ ቁጥሮች ሲጠሩ ካርዱ ላይ ምልክት ይደረጋል። መስመር (ወደጎን፣ ወደታች ወይም ዲያጎናል) ወይም 4ቱን ማዕዘኖች የሞላ ካርቴላ ያሸንፋል።\n5️⃣ አሸናፊው ከጠቅላላው ድርሻ ${Math.round(CUT * 100)}% ያገኛል። ጨዋታ ለመጀመር ቢያንስ 2 ተጫዋች ያስፈልጋል።\n6️⃣ ለማውጣት «አውጣ» ን ይጫኑ (ቢያንስ ${MIN_WD} ብር)።\n\nጥያቄ ካለዎት: ${SUPPORT}`;
const KBNOTE = '⌨️ አዲስ! ከታች ያሉትን ቁልፎች (ጨዋታ ተጫወት፣ ገንዘብ አስገባ፣ ቀሪ ሂሳብ) መጠቀም ይችላሉ።';

// banks offered in the deposit / withdraw flows
const BANKS = { cbe: 'CBE', telebirr: 'TELEBIRR', mpesa: 'M-PESA', ebirr: 'E-BIRR' }; // DEPOSIT: only these 4 accounts of ours
const WD_BANKS = { cbe: 'CBE', dashen: 'DASHEN', oromia: 'OROMIA BANK', awash: 'AWASH BANK', boa: 'BOA', mpesa: 'M-PESA', telebirr: 'TELEBIRR', ebirr: 'E-BIRR' }; // WITHDRAW: the player can receive money in any of these
const BANK_DEF = { cbe: { a: '0982535736', h: 'kidus' }, telebirr: { a: '0900060528', h: 'kidus' }, mpesa: { a: '0722251380', h: 'likinaw' }, ebirr: { a: '0982535736', h: 'kidus' } }; // used until the admin saves an account (Admin > Accounts)
let ACC = { ...BANK_DEF }; // the accounts players pay into; refreshed from the database at the start of every bot update (loadAcc)
async function loadAcc(env) { let s = {}; try { s = JSON.parse(((await env.DB.prepare("SELECT v FROM settings WHERE k='accounts'").first()) || {}).v || '{}') || {} } catch (e) { } const o = {}; for (const k of Object.keys(BANKS)) { const v = s[k]; o[k] = v && v.a ? { a: String(v.a), h: String(v.h || '') } : { ...BANK_DEF[k] } } return ACC = o }
async function accountsFor(env, url, all) { await loadAcc(env); const im = {}; try { for (const r of (await env.DB.prepare('SELECT bank,ts FROM account_imgs').all()).results) im[r.bank] = r.ts } catch (e) { } const o = {}; for (const k of Object.keys(BANKS)) if (all || ACC[k].a) o[k] = { a: ACC[k].a, h: ACC[k].h, img: im[k] ? `${url.origin}/acc/${k}.jpg?v=${im[k]}` : IMG_DEF[k] ? `${url.origin}/acc/${k}.jpg?v=0` : '' }; return o }
const banksFor = (env, flow) => Object.keys(flow === 'w' ? WD_BANKS : BANKS);
const bankKb = (env, flow) => {
  const names = flow === 'w' ? WD_BANKS : BANKS, b = banksFor(env, flow).map(k => ({ text: names[k], callback_data: `b:${flow}:${k}` })), rows = [];
  for (let i = 0; i < b.length; i += 2) rows.push(b.slice(i, i + 2));
  rows.push([{ text: '❌ ሰርዝ', callback_data: 'b:x' }]);
  return { inline_keyboard: rows };
};
const acctText = (env, k) => { const x = ACC[k] || { a: '', h: '' }; return (k === 'cbe' ? '🏦 ንግድ ባንክ (CBE): ' : k === 'telebirr' ? '📱 ቴሌብር: ' : k === 'boa' ? '🏦 አቢሲኒያ ባንክ (BOA): ' : k === 'mpesa' ? '📱 ኤም-ፔሳ (M-Pesa): ' : '📱 ኢ-ብር (E-birr): ') + x.a + (x.h ? '\n👤 ስም: ' + x.h : '') };
// plain account number of a bank (used by the copy button)
const acctNo = (env, k) => (ACC[k] && ACC[k].a) || '';
// sends a photo from the saved picture (data URL) with a caption and optional inline buttons
const sendPhotoData = (env, chat, dataUrl, caption, markup) => { try { const bytes = Uint8Array.from(atob(String(dataUrl).split(',')[1]), c => c.charCodeAt(0)), fd = new FormData(); fd.append('chat_id', String(chat)); fd.append('caption', caption); fd.append('photo', new Blob([bytes], { type: 'image/jpeg' }), 'account.jpg'); if (markup) fd.append('reply_markup', JSON.stringify(markup)); return fetch(`https://api.telegram.org/bot${env.BOT_TOKEN}/sendPhoto`, { method: 'POST', body: fd }).catch(() => null) } catch (e) { return Promise.resolve(null) } };
// inline buttons that copy the account number and the amount with one tap (Telegram copy_text button)
const copyKb = (env, k, amt) => { const no = acctNo(env, k), rows = []; if (no) rows.push([{ text: '📋 የአካውንት ቁጥር ኮፒ: ' + no, copy_text: { text: no } }]); if (amt) rows.push([{ text: '📋 መጠን ኮፒ: ' + amt + ' ብር', copy_text: { text: String(amt) } }]); return rows.length ? { inline_keyboard: rows } : undefined };

// where a player is in a multi-step flow (deposit / withdraw / transfer); expires after 30 minutes
const setState = (env, uid, step, data) => env.DB.prepare('INSERT INTO bot_state(uid,step,data,ts) VALUES(?1,?2,?3,?4) ON CONFLICT(uid) DO UPDATE SET step=?2,data=?3,ts=?4').bind(uid, step, JSON.stringify(data || {}), Date.now()).run();
const getState = async (env, uid) => { const r = await env.DB.prepare('SELECT step,data,ts FROM bot_state WHERE uid=?').bind(uid).first(); if (!r || Date.now() - r.ts > 30 * 60 * 1000) return null; let d = {}; try { d = JSON.parse(r.data || '{}') } catch (e) { } return { ...d, step: r.step } };
const clearState = (env, uid) => env.DB.prepare('DELETE FROM bot_state WHERE uid=?').bind(uid).run();
const hasDeposit = async (env, uid) => !!(await env.DB.prepare("SELECT 1 x FROM deposits WHERE user_id=? AND status='approved' LIMIT 1").bind(uid).first());

async function onContact(env, m) { // the player shared their phone number: register (no bonus) and show the play buttons
  const db = env.DB, uid = m.from.id, c = m.contact, now = Date.now();
  if (c.user_id && Number(c.user_id) !== Number(uid)) return sendTo(env, uid, '⚠️ እባክዎ የራስዎን ስልክ ቁጥር ብቻ ያጋሩ።', SHARE_KB);
  const ph = normPhone(c.phone_number);
  if (!ph) return sendTo(env, uid, '⚠️ ይህ ስልክ ቁጥር ትክክል አይደለም። የኢትዮጵያ ቁጥር (09… ወይም 07…) ያስፈልጋል።', SHARE_KB);
  const nm = String(c.first_name || m.from.first_name || 'player').trim().slice(0, 30) || 'player';
  await db.prepare('INSERT INTO users(id,name,created_ts) VALUES(?,?,?) ON CONFLICT(id) DO NOTHING').bind(uid, nm, now).run();
  const u = await db.prepare('SELECT phone FROM users WHERE id=?').bind(uid).first();
  if (u && u.phone) { await sendBottom(env, uid, '✅ አስቀድመው ተመዝግበዋል።'); return sendMenu(env, uid, '🎮 ከታች ካሉት አማራጮች ይምረጡ።') }
  let ok = false;
  try { ok = (await db.prepare("UPDATE users SET name=?1,phone=?2 WHERE id=?3 AND (phone IS NULL OR phone='')").bind(nm, ph, uid).run()).meta.changes > 0 }
  catch (e) { return sendTo(env, uid, `⚠️ ይህ ስልክ ቁጥር በሌላ አካውንት ተመዝግቧል። ለእርዳታ ${SUPPORT} ያነጋግሩ።`, SHARE_KB) }
  if (!ok) { await sendBottom(env, uid, '✅ አስቀድመው ተመዝግበዋል።'); return sendMenu(env, uid, '🎮 ከታች ካሉት አማራጮች ይምረጡ።') }
  await sendBottom(env, uid, 'እንኳን ደስ አሎት ተመዝግበዋል'); // the bottom keyboard (play buttons)
  return sendMenu(env, uid, '🎮 ከታች ካሉት አማራጮች ይምረጡ።'); // the inline menu with the Play button
}

/* ---------- money operations (each is one atomic batch) ---------- */
// tells every admin HOW a deposit was credited automatically: "✅ Approved by verify.et", "✅ Approved by SMS match" or "✅ Approved by SMS + verify.et"
async function tellAdminsApproved(env, id, how) {
  const d = await env.DB.prepare('SELECT d.amount_c,d.method,d.txid,u.name,u.phone FROM deposits d JOIN users u ON u.id=d.user_id WHERE d.id=?').bind(id).first(); if (!d) return;
  const lab = how === 'verify.et' ? '✅ Approved by verify.et' : how === 'sms+verify.et' ? '✅ Approved by SMS + verify.et (ሁለቱም ተስማምተዋል)' : '✅ Approved by SMS match';
  await notifyAdmins(env, `${lab}\n💰 ገቢ #${id}\n${d.name} · ${d.phone}\nመጠን: ${B(d.amount_c)} ብር በ ${d.method}\nየግብይት ቁጥር: ${d.txid}`);
}
async function tryMatch(env, txid) { // credit a pending deposit when a matching unclaimed SMS exists (never when the deposit is held for the admin: verify_log verdict 'bad' or 'hold')
  await ensureTables(env);
  const db = env.DB, held = "NOT EXISTS(SELECT 1 FROM verify_log v WHERE v.txid=?1 AND v.verdict IN('bad','hold'))";
  const r = await db.batch([
    db.prepare("UPDATE users SET balance=balance+(SELECT d.amount_c FROM deposits d WHERE d.txid=?1) WHERE id=(SELECT d.user_id FROM deposits d JOIN sms_log s ON s.txid=d.txid WHERE d.txid=?1 AND d.status='pending' AND s.claimed=0 AND s.amount_c=d.amount_c AND " + held + ")").bind(txid),
    db.prepare("UPDATE deposits SET status='approved',note='sms' WHERE txid=?1 AND status='pending' AND EXISTS(SELECT 1 FROM sms_log s WHERE s.txid=?1 AND s.claimed=0 AND s.amount_c=deposits.amount_c) AND " + held).bind(txid),
    db.prepare("UPDATE sms_log SET claimed=1 WHERE txid=?1 AND claimed=0 AND EXISTS(SELECT 1 FROM deposits d WHERE d.txid=?1 AND d.status='approved')").bind(txid)]);
  if (r[1].meta.changes > 0) {
    const d = await db.prepare('SELECT id,user_id,amount_c FROM deposits WHERE txid=?').bind(txid).first();
    const v = await db.prepare('SELECT verdict FROM verify_log WHERE txid=?').bind(txid).first().catch(() => null), how = v && v.verdict === 'ok' ? 'sms+verify.et' : 'sms';
    if (how !== 'sms') await db.prepare('UPDATE deposits SET note=?2 WHERE id=?1').bind(d.id, how).run().catch(() => { });
    await say(env, d.user_id, `✅ ${B(d.amount_c)} ብር ገቢ ተደርጎልሀል`, playKb(env)); // awaited: a message that is not awaited can be cut off when the Worker finishes
    await tellAdminsApproved(env, d.id, how);
    return true;
  }
  return false;
}
// force = true when the admin presses ✅ አጽድቅ on a HELD deposit (the button exists only for held deposits, unless ALLOW_MANUAL_DEPOSIT=1)
async function decideDeposit(env, id, ok, force) {
  const db = env.DB;
  if (ok && !manualDep(env) && !force) return false; // safety: no manual approval of deposits while it is locked
  const r = await db.batch(ok ? [
    db.prepare("UPDATE users SET balance=balance+(SELECT amount_c FROM deposits WHERE id=?1 AND status='pending') WHERE id=(SELECT user_id FROM deposits WHERE id=?1 AND status='pending')").bind(id),
    db.prepare("UPDATE deposits SET status='approved',note='admin' WHERE id=?1 AND status='pending'").bind(id)
  ] : [db.prepare("UPDATE deposits SET status='rejected',note='admin' WHERE id=?1 AND status='pending'").bind(id)]);
  const done = r[r.length - 1].meta.changes > 0;
  if (done) { const d = await db.prepare('SELECT user_id,amount_c FROM deposits WHERE id=?').bind(id).first(); await say(env, d.user_id, ok ? `✅ ${B(d.amount_c)} ብር ገቢ ተደርጎልሀል` : `❌ ገቢዎ ውድቅ ተደርጓል። ለእርዳታ ${SUPPORT} ያነጋግሩ።`, ok ? playKb(env) : undefined) }
  return done;
}
async function decideWithdraw(env, id, paid) {
  const db = env.DB;
  const r = await db.batch(paid ? [db.prepare("UPDATE withdrawals SET status='paid' WHERE id=?1 AND status='pending'").bind(id)] : [
    db.prepare("UPDATE users SET balance=balance+(SELECT amount_c FROM withdrawals WHERE id=?1 AND status='pending') WHERE id=(SELECT user_id FROM withdrawals WHERE id=?1 AND status='pending')").bind(id),
    db.prepare("UPDATE withdrawals SET status='rejected' WHERE id=?1 AND status='pending'").bind(id)]);
  const done = r[r.length - 1].meta.changes > 0;
  if (done) { const w = await db.prepare('SELECT user_id,amount_c FROM withdrawals WHERE id=?').bind(id).first(); await say(env, w.user_id, paid ? `✅ ${B(w.amount_c)} ብር ተልኮልዎታል።` : `↩️ የማውጣት ጥያቄዎ ውድቅ ተደርጓል — ${B(w.amount_c)} ብር ወደ ቀሪ ሂሳብዎ ተመልሷል።`) }
  return done;
}

/* ---------- verify.et: automatic deposit check ----------
   Answers 'ok' only when the receipt is real AND the amount equals the claimed amount AND the money went to OUR account AND the receipt is not older than 72 hours.
   'bad' = it clearly disagrees (the credit is held for the admin). 'unknown' = no clear answer (nothing is credited, nothing is rejected).
   Telebirr and M-Pesa are sent. One call costs one verify.et credit, so it runs once per deposit and only when VERIFYET_KEY is set and the amount is at least VERIFYET_MIN birr (default 0). */
const VET_BANK = { telebirr: 'telebirr', mpesa: 'mpesa' };
const vetMax = env => env.VERIFYET_AUTO_MAX === undefined || env.VERIFYET_AUTO_MAX === '' ? 1000 : Number(env.VERIFYET_AUTO_MAX); // the biggest deposit verify.et may credit ALONE (0 = never alone)
async function vetCheck(env, bank, txid, amount_c) {
  const code = VET_BANK[bank];
  if (!env.VERIFYET_KEY || !code || amount_c < C(env.VERIFYET_MIN ?? 0)) return { verdict: 'skip', note: '' };
  try {
    const r = await fetch('https://verify.et/api/verify?waitMs=5000', { method: 'POST',
      headers: { 'content-type': 'application/json', 'x-api-key': env.VERIFYET_KEY, 'Idempotency-Key': 'aman-' + bank + '-' + txid },
      body: JSON.stringify({ bank: code, transactionNumber: txid, settlementAccount: (ACC[bank] || {}).a || undefined }), signal: AbortSignal.timeout(9000) });
    const j = await r.json().catch(() => null), d = j && Array.isArray(j.data) ? j.data[0] : null;
    if (r.status === 402) return { verdict: 'unknown', note: 'verify.et: ክሬዲት አልቋል — ምንም አልተረጋገጠም' };
    if (r.status !== 200 || !d) return { verdict: 'unknown', note: 'verify.et: ግልጽ መልስ አልሰጠም (' + r.status + ')' };
    const st = String(d.status || (j.verification && j.verification.status) || '').toLowerCase();
    if (d.verified !== true) return /not_?found|fail|invalid|reject/.test(st) ? { verdict: 'bad', note: 'verify.et: 🚨 ግብይቱ አልተገኘም / አልተረጋገጠም (' + st + ')' } : { verdict: 'unknown', note: 'verify.et: ገና አልተረጋገጠም (' + (st || '?') + ')' };
    if (d.amount == null || !Number.isFinite(Number(d.amount))) return { verdict: 'unknown', note: 'verify.et: መጠኑን አልመለሰም' };
    if (Math.abs(C(d.amount) - amount_c) > 1) return { verdict: 'bad', note: 'verify.et: 🚨 መጠን ይለያል — እውነተኛው ደረሰኝ ' + Number(d.amount) + ' ብር' };
    const ds = String(d.date || d.transactionDate || d.paymentDate || d.paidAt || d.createdAt || ''), tt = /^\d{4}-\d{2}-\d{2}/.test(ds) ? Date.parse(ds) : NaN; // only an ISO date is trusted (other formats are ambiguous)
    if (Number.isFinite(tt) && Date.now() - tt > 72 * 36e5) return { verdict: 'bad', note: 'verify.et: 🚨 ደረሰኙ ከ72 ሰዓት በላይ ያረጀ ነው (አሮጌ ደረሰኝ ሊሆን ይችላል)' };
    const m = d.settlementAccountMatch;
    if (m && m.matched === false && m.reason === 'candidate_account_mismatch') return { verdict: 'bad', note: 'verify.et: 🚨 ገንዘቡ ወደ እኛ አካውንት አልገባም' };
    if (m && m.matched === true) return { verdict: 'ok', note: 'verify.et: ✅ ደረሰኙ እውነተኛ ነው፣ መጠኑ እና የእኛ አካውንት ተመሳሳይ ናቸው' };
    return { verdict: 'unknown', note: 'verify.et: ደረሰኙ እውነተኛ ነው ግን የተቀባዩ አካውንት አልተረጋገጠም' };
  } catch (e) { return { verdict: 'unknown', note: 'verify.et: ግንኙነት አልተሳካም' } }
}
// decides whether the automatic credit must wait for the admin. Writes the result to verify_log (tryMatch reads it).
async function vetGate(env, u, amount_c, bank, txid) {
  await ensureTables(env);
  const v = await vetCheck(env, bank, txid, amount_c); let hold = '';
  if (v.verdict === 'bad') hold = v.note;
  else if (amount_c > C(env.FIRST_DEP_MAX ?? 1000) && !(await hasDeposit(env, u.id))) hold = '🆕 የመጀመሪያ ትልቅ ገቢ (' + B(amount_c) + ' ብር) — አስተዳዳሪ በእጅ ማጽደቅ አለበት';
  if (!hold) { // repeat-offender and daily-limit guards
    const h = await env.DB.prepare("SELECT COALESCE(SUM(status='rejected'),0) rej,COALESCE(SUM(CASE WHEN status='approved' AND note='verify.et' AND ts>?2 THEN amount_c END),0) vet FROM deposits WHERE user_id=?1").bind(u.id, Date.now() - 864e5).first();
    if (h.rej >= 2) hold = '🚫 ይህ ተጫዋች ' + h.rej + ' ጊዜ ውድቅ የተደረገ ገቢ አለው — አስተዳዳሪ ብቻ ያጽድቃል';
    else if (v.verdict === 'ok' && h.vet + amount_c > C(env.VET_DAILY_MAX ?? 3000)) hold = '📈 በverify.et ብቻ በ24 ሰዓት የገባው ከ' + (env.VET_DAILY_MAX ?? 3000) + ' ብር በላይ ሆኗል — አስተዳዳሪ በእጅ ማጽደቅ አለበት';
  }
  if (hold || v.verdict !== 'skip') await env.DB.prepare('INSERT OR REPLACE INTO verify_log(txid,bank,verdict,detail,ts) VALUES(?,?,?,?,?)').bind(txid, bank, hold ? (v.verdict === 'bad' ? 'bad' : 'hold') : v.verdict, (hold ? hold + (v.note && v.note !== hold ? ' · ' + v.note : '') : v.note).slice(0, 300), Date.now()).run().catch(() => { });
  return { hold, note: v.note, verdict: v.verdict };
}
// credits a pending deposit once, because verify.et confirmed it. Guarded by status='pending' so it can never pay twice, even together with the SMS match.
async function autoApprove(env, id) {
  const db = env.DB;
  const r = await db.batch([
    db.prepare("UPDATE users SET balance=balance+(SELECT amount_c FROM deposits WHERE id=?1 AND status='pending') WHERE id=(SELECT user_id FROM deposits WHERE id=?1 AND status='pending')").bind(id),
    db.prepare("UPDATE deposits SET status='approved',note='verify.et' WHERE id=?1 AND status='pending'").bind(id)]);
  if (r[1].meta.changes > 0) {
    const d = await db.prepare('SELECT user_id,amount_c,txid FROM deposits WHERE id=?').bind(id).first();
    await db.prepare('INSERT INTO admin_log(ts,actor,action,detail) VALUES(?,?,?,?)').bind(Date.now(), 'verify.et', 'auto credit', 'deposit #' + id + ' · ' + B(d.amount_c) + ' birr · tx ' + d.txid).run().catch(() => { });
    await say(env, d.user_id, `✅ ${B(d.amount_c)} ብር ገቢ ተደርጎልሀል`, playKb(env));
    await tellAdminsApproved(env, id, 'verify.et'); // the admin message says: Approved by verify.et
    return true;
  }
  return false;
}
// manual approval: LOCKED by default. A HELD deposit (verify_log verdict 'bad' / 'hold') always gets the ✅ አጽድቅ button, because only the admin can decide it.
const manualDep = env => env.ALLOW_MANUAL_DEPOSIT === '1';
const isHeld = async (env, txid) => { try { await ensureTables(env); const v = await env.DB.prepare('SELECT verdict FROM verify_log WHERE txid=?').bind(txid).first(); return !!v && (v.verdict === 'bad' || v.verdict === 'hold') } catch (e) { return false } };
const heldById = async (env, id) => { const d = await env.DB.prepare("SELECT txid FROM deposits WHERE id=? AND status='pending'").bind(id).first(); return !!d && await isHeld(env, d.txid) };
// buttons under a pending deposit message for the admin (the verify.et button only where verify.et can check that bank; ✅ አጽድቅ only when the deposit is held)
const depKb = (env, id, bank, held) => { const r = (manualDep(env) || held) ? [{ text: '✅ አጽድቅ', callback_data: 'da:' + id }, { text: '❌ ውድቅ', callback_data: 'dr:' + id }] : [{ text: '❌ ውድቅ', callback_data: 'dr:' + id }]; return env.VERIFYET_KEY && VET_BANK[bank] ? [r, [{ text: '🔎 verify.et እንደገና ፈትሽ', callback_data: 'dv:' + id }]] : [r] };
// the admin presses "verify.et": run the whole check again for one pending deposit; credits it only if every automatic rule passes
async function recheckDeposit(env, id) {
  const db = env.DB, d = await db.prepare("SELECT d.*,u.name,u.phone,u.created_ts FROM deposits d JOIN users u ON u.id=d.user_id WHERE d.id=? AND d.status='pending'").bind(id).first();
  if (!d) return { ok: false, text: 'ቀድሞ ተከናውኗል (ይህ ገቢ በመጠባበቅ ላይ አይደለም)' };
  if (!env.VERIFYET_KEY || !VET_BANK[d.method]) return { ok: false, text: 'verify.et ይህን ባንክ አይፈትሽም (' + d.method + ')' };
  const u = { id: d.user_id, name: d.name, phone: d.phone, created_ts: d.created_ts };
  await ensureTables(env); await db.prepare('DELETE FROM verify_log WHERE txid=?').bind(d.txid).run().catch(() => { });
  const gate = await vetGate(env, u, d.amount_c, d.method, d.txid), vmax = vetMax(env);
  let ok = await tryMatch(env, d.txid);
  if (!ok && !gate.hold && gate.verdict === 'ok' && vmax > 0 && d.amount_c <= C(vmax)) ok = await autoApprove(env, id);
  if (ok) return { ok: true, text: '✅ ተጠናቋል — ገቢው ተጨምሯል' };
  return { ok: false, text: (gate.hold ? '⛔ ' + gate.hold : gate.note || 'verify.et ምንም አላረጋገጠም') + (gate.hold ? '' : gate.verdict === 'ok' ? '\n(በverify.et ብቻ ለማጽደቅ መጠኑ ከ' + vmax + ' ብር በላይ ነው — በእጅ ያጽድቁ)' : '') };
}
// a deposit request (from the app or from the bot): auto-credited when a matching bank SMS was already forwarded to /sms, otherwise sent to the admins and credited the moment the SMS arrives.
async function makeDeposit(env, u, amt, txid, method) {
  const db = env.DB, now = Date.now(); let id;
  if ((await db.prepare("SELECT COUNT(*) c FROM deposits WHERE user_id=? AND status='pending'").bind(u.id).first()).c >= 3) return { error: 'too_many_pending' }; // fake-claim guard: no more than 3 unconfirmed requests per player
  try { id = (await db.prepare('INSERT INTO deposits(user_id,txid,amount_c,method,status,ts) VALUES(?,?,?,?,?,?)').bind(u.id, txid, C(amt), method, 'pending', now).run()).meta.last_row_id } catch (e) { return { error: 'txid_used' } }
  const gate = await vetGate(env, u, C(amt), method, txid); // verify.et second opinion + safety guards (written before the SMS match is tried)
  let ok = await tryMatch(env, txid);
  const vmax = vetMax(env);
  if (!ok && !gate.hold && gate.verdict === 'ok' && vmax > 0 && C(amt) <= C(vmax)) ok = await autoApprove(env, id); // second way to be credited automatically: verify.et confirmed it
  if (!ok) await notifyAdmins(env, depositText({ manual: (manualDep(env) || gate.hold) ? '1' : '', id, name: u.name, phone: u.phone, amount_c: C(amt), method, txid, held: gate.hold, flags: await depositChecks(env, u, { amount_c: C(amt), method, txid }, gate) }), depKb(env, id, method, !!gate.hold));
  return { status: ok ? 'approved' : 'pending', id, held: !!gate.hold };
}
// Fake-text scan: for a deposit that is NOT matched, the admin gets these checks so a forged claim is easy to spot before pressing Approve.
async function depositChecks(env, u, d, gate) {
  const db = env.DB, f = [], t = d.txid;
  if (gate && gate.hold) f.push('⛔ ራስ-ሰር መጨመር ተቆልፏል — አስተዳዳሪ ብቻ ያጸድቃል: ' + gate.hold);
  else if (gate && gate.note) f.push('🔎 ' + gate.note);
  const s = await db.prepare('SELECT amount_c FROM sms_log WHERE txid=?').bind(t).first();
  if (!s) f.push('❌ ከባንክ የተላከ ተዛማጅ SMS አልደረሰም — ገንዘቡ በእርግጥ መግባቱን በባንክ አፕዎ ካላረጋገጡ አያጽድቁ');
  else if (s.amount_c !== d.amount_c) f.push(`🚨 መጠን አይመሳሰልም! በእውነተኛው SMS ላይ ${B(s.amount_c)} ብር፣ ተጫዋቹ ግን ${B(d.amount_c)} ብር ብሏል — የተቀየረ መልዕክት ሊሆን ይችላል`);
  else f.push('✅ የባንክ SMS ደርሷል፣ መጠኑ እና የግብይት ቁጥሩ ተመሳሳይ ናቸው');
  const okfmt = d.method === 'telebirr' ? /^[A-Z0-9]{10}$/.test(t) : d.method === 'boa' || d.method === 'cbe' ? /^FT[A-Z0-9]{10}$/.test(t) : /^[A-Z0-9]{8,24}$/.test(t);
  if (!okfmt) f.push(`⚠️ የግብይት ቁጥሩ ለ${BANKS[d.method] || d.method} ያልተለመደ ነው (${t})`);
  const h = await db.prepare("SELECT COALESCE(SUM(status='approved'),0) ok,COALESCE(SUM(status='rejected'),0) rej FROM deposits WHERE user_id=? AND txid<>?").bind(u.id, t).first();
  f.push(`👤 ቀድሞ የጸደቁ ገቢዎች: ${h.ok} · ውድቅ የተደረጉ: ${h.rej}` + (Date.now() - (u.created_ts || Date.now()) < 864e5 ? ' · 🆕 አዲስ አካውንት (ከ24 ሰዓት በታች)' : '') + (h.ok === 0 ? ' · የመጀመሪያ ገቢ' : ''));
  return f.join('\n');
}
// what the admin sees under a withdrawal request: how much this player really deposited and HOW it was approved (the two reads run together)
async function wdInfo(env, uid) {
  const [r, w] = await Promise.all([
    env.DB.prepare("SELECT COALESCE(SUM(CASE WHEN status='approved' THEN amount_c END),0) dep,COALESCE(SUM(CASE WHEN status='approved' AND note='admin' THEN amount_c END),0) adm,COALESCE(SUM(CASE WHEN status='approved' AND note='verify.et' THEN amount_c END),0) vet,COALESCE(SUM(status='approved'),0) n FROM deposits WHERE user_id=?").bind(uid).first(),
    env.DB.prepare("SELECT COALESCE(SUM(amount_c),0) paid FROM withdrawals WHERE user_id=? AND status='paid'").bind(uid).first()]);
  return `📊 ጠቅላላ የጸደቀ ገቢ: ${B(r.dep)} ብር (${r.n} ጊዜ) · ቀድሞ የተከፈለ: ${B(w.paid)} ብር\n   በአስተዳዳሪ በእጅ የጸደቀ: ${B(r.adm)} · በverify.et ብቻ የጸደቀ: ${B(r.vet)}`;
}
// a withdrawal request: balance is taken now and given back if an admin rejects it
async function makeWithdrawal(env, u, amt, account, method) {
  const db = env.DB, now = Date.now(); method = String(method || 'telebirr').slice(0, 20);
  if (!(await hasDeposit(env, u.id))) return { error: 'deposit_required' }; // bonus-farming guard: deposit once before withdrawing
  let id; try { const r = await db.batch([db.prepare('UPDATE users SET balance=balance-?2 WHERE id=?1').bind(u.id, C(amt)), db.prepare('INSERT INTO withdrawals(user_id,amount_c,method,account,status,ts) VALUES(?,?,?,?,?,?)').bind(u.id, C(amt), method, account, 'pending', now)]); id = r[1].meta.last_row_id } catch (e) { return { error: errOf(e) } }
  const info = await wdInfo(env, u.id).catch(() => '');
  await notifyAdmins(env, withdrawText({ id, name: u.name, phone: u.phone, amount_c: C(amt), method, account, info }), [[{ text: '💸 ተከፍሏል', callback_data: 'wp:' + id }, { text: '↩️ ውድቅ', callback_data: 'wr:' + id }]]);
  return { id };
}
// player-to-player transfer: both statements test the sender's balance at the same moment, so either both apply or neither does
async function makeTransfer(env, u, to, amt) {
  const db = env.DB, c = C(amt);
  const r = await db.batch([
    db.prepare('UPDATE users SET balance=balance+?1 WHERE id=?3 AND id<>?2 AND (SELECT balance FROM users WHERE id=?2)>=?1').bind(c, u.id, to),
    db.prepare('UPDATE users SET balance=balance-?1 WHERE id=?2 AND (SELECT balance FROM users WHERE id=?2)>=?1 AND EXISTS(SELECT 1 FROM users WHERE id=?3 AND id<>?2)').bind(c, u.id, to)]);
  return r[1].meta.changes > 0 ? { ok: true } : { error: 'insufficient_balance' };
}

/* ---------- settings, bans and admin log (tables are created ONCE ever, then a marker is stored) ---------- */
let tablesReady = false;
const SCHEMA_MARK = 'schema_v2';
const INDEXES = [ // speed: the players list, deposits, withdrawals, rounds and picks are looked up by these columns
  'CREATE INDEX IF NOT EXISTS idx_users_created ON users(created_ts)',
  'CREATE INDEX IF NOT EXISTS idx_dep_user ON deposits(user_id,status)',
  'CREATE INDEX IF NOT EXISTS idx_dep_status ON deposits(status,ts)',
  'CREATE INDEX IF NOT EXISTS idx_wd_user ON withdrawals(user_id,status)',
  'CREATE INDEX IF NOT EXISTS idx_wd_status ON withdrawals(status)',
  'CREATE INDEX IF NOT EXISTS idx_rounds_status ON rounds(status,ended_ts)',
  'CREATE INDEX IF NOT EXISTS idx_picks_user ON picks(round_id,user_id)'];
const ensureTables = async env => {
  if (tablesReady) return;
  let ok = false; try { ok = !!(await env.DB.prepare('SELECT 1 x FROM settings WHERE k=?').bind(SCHEMA_MARK).first()) } catch (e) { }
  if (!ok) { // first run after this update (or a brand-new database): create everything once
    await env.DB.batch([
      env.DB.prepare('CREATE TABLE IF NOT EXISTS settings(k TEXT PRIMARY KEY,v TEXT)'),
      env.DB.prepare('CREATE TABLE IF NOT EXISTS bans(id INTEGER PRIMARY KEY)'),
      env.DB.prepare('CREATE TABLE IF NOT EXISTS admins(id INTEGER PRIMARY KEY,added_ts INTEGER)'),
      env.DB.prepare('CREATE TABLE IF NOT EXISTS admin_log(id INTEGER PRIMARY KEY AUTOINCREMENT,ts INTEGER,actor TEXT,action TEXT,detail TEXT)'),
      env.DB.prepare('CREATE TABLE IF NOT EXISTS bot_state(uid INTEGER PRIMARY KEY,step TEXT,data TEXT,ts INTEGER)'),
      env.DB.prepare('CREATE TABLE IF NOT EXISTS kb_sent(uid INTEGER PRIMARY KEY)'), // players who already received the bottom keyboard
      env.DB.prepare('CREATE TABLE IF NOT EXISTS referrals(user_id INTEGER PRIMARY KEY,ref_id INTEGER,ts INTEGER)'),
      env.DB.prepare('CREATE TABLE IF NOT EXISTS bonus_wins(round_id INTEGER,cartela INTEGER,user_id INTEGER,name TEXT,amount_c INTEGER,paid INTEGER DEFAULT 0,ts INTEGER,PRIMARY KEY(round_id,cartela))'),
      env.DB.prepare('CREATE TABLE IF NOT EXISTS wk_games(week INTEGER,user_id INTEGER,games INTEGER DEFAULT 0,PRIMARY KEY(week,user_id))'), // games played per player in a weekly-bonus period
      env.DB.prepare('CREATE INDEX IF NOT EXISTS idx_wk_games ON wk_games(week,games DESC)'),
      env.DB.prepare('CREATE TABLE IF NOT EXISTS wk_paid(week INTEGER PRIMARY KEY,ts INTEGER)'), // periods whose prizes were already paid (a period can be paid only once)
      env.DB.prepare('CREATE TABLE IF NOT EXISTS wk_winners(week INTEGER,pos INTEGER,user_id INTEGER,name TEXT,prize_c INTEGER,games INTEGER,PRIMARY KEY(week,pos))'),
      env.DB.prepare('CREATE TABLE IF NOT EXISTS verify_log(txid TEXT PRIMARY KEY,bank TEXT,verdict TEXT,detail TEXT,ts INTEGER)'), // verify.et second opinion per deposit; bad / hold = automatic credit is blocked
      env.DB.prepare('CREATE TABLE IF NOT EXISTS account_imgs(bank TEXT PRIMARY KEY,data TEXT,ts INTEGER)')]); // deposit account pictures
    try { await env.DB.prepare('SELECT auto_off FROM users LIMIT 1').first() } catch (e) { try { await env.DB.prepare('ALTER TABLE users ADD COLUMN auto_off INTEGER DEFAULT 0').run() } catch (e2) { } }
    for (const sql of INDEXES) { try { await env.DB.prepare(sql).run() } catch (e) { } } // one failing index never blocks the others
    try { await env.DB.prepare('INSERT OR REPLACE INTO settings(k,v) VALUES(?,?)').bind(SCHEMA_MARK, '1').run() } catch (e) { }
  }
  try { // ONE TIME: replace the accounts saved before with the new ones (BANK_DEF); after this the admin's own changes are kept
    if (!(await env.DB.prepare("SELECT 1 x FROM settings WHERE k='acc_v3'").first())) await env.DB.batch([
      env.DB.prepare("INSERT OR REPLACE INTO settings(k,v) VALUES('accounts',?)").bind(JSON.stringify(BANK_DEF)),
      env.DB.prepare("DELETE FROM account_imgs WHERE bank='boa'"),
      env.DB.prepare("INSERT OR REPLACE INTO settings(k,v) VALUES('acc_v3','1')")]);
  } catch (e) { }
  tablesReady = true };
const cfg = { t: 0, set: {}, bans: new Set() }; // settings and bans are cached for 5 seconds to keep requests fast
const loadCfg = async env => { if (Date.now() - cfg.t < 5000) return cfg; await ensureTables(env); const [a, b] = await env.DB.batch([env.DB.prepare('SELECT k,v FROM settings'), env.DB.prepare('SELECT id FROM bans')]); cfg.set = Object.fromEntries(a.results.map(r => [r.k, r.v])); cfg.bans = new Set(b.results.map(r => String(r.id))); cfg.t = Date.now(); return cfg };
const getSet = async (env, k) => (await loadCfg(env)).set[k] ?? null;
const setSet = async (env, k, v) => { await ensureTables(env); await env.DB.prepare('INSERT INTO settings(k,v) VALUES(?1,?2) ON CONFLICT(k) DO UPDATE SET v=excluded.v').bind(k, v).run(); cfg.t = 0 };
const isBanned = async (env, id) => (await loadCfg(env)).bans.has(String(id));

/* ---------- WEEKLY BONUS switch (the admin decides when it starts and stops) ----------
   Stored in settings.wk_cfg = {"on":true,"start":<ms>,"end":<ms>}. It is RUNNING only while on && start<=now<end.
   Games are counted (wk_games, keyed by the start time) only while it is running. When it stops or ends, the period stays in the database so the admin can pay its winners. */
const wkCfg = async env => { try { const c = JSON.parse(await getSet(env, 'wk_cfg') || 'null') || {}; return { on: !!c.on, start: Number(c.start) || 0, end: Number(c.end) || 0 } } catch (e) { return { on: false, start: 0, end: 0 } } };
const wkRunning = (c, now) => !!(c.on && c.start > 0 && now >= c.start && now < c.end);

/* ---------- secret bonus (admin chooses cartelas for one round; the taker wins at once) ----------
   Stored in settings as {"on":true,"round":12,"items":[{"c":7,"a":5000}]} (a = cents). The GameHub reads it from the database when a lobby is loaded or after the admin saves
   (invalidate), and keeps it in memory, so a pick no longer needs a database read for it. The cartela numbers are never sent to the players. */
const readBonus = async env => { await ensureTables(env); const r = await env.DB.prepare("SELECT v FROM settings WHERE k='bonus'").first(); try { const c = r && JSON.parse(r.v); return c && c.on && Array.isArray(c.items) && c.items.length ? c : null } catch (e) { return null } };
const bonusFor = async (env, roundId) => { const c = await readBonus(env); return c && c.round === roundId ? c : null };
// pays the bonus to the player who just took the cartela. One batch: the win row is created once, the balance is added only while paid=0, then paid=1 — so it can never pay twice.
async function awardBonus(env, roundId, no, u, amount_c) {
  const db = env.DB;
  for (let t = 0; t < 2; t++) {
    try {
      const r = await db.batch([
        db.prepare('INSERT OR IGNORE INTO bonus_wins(round_id,cartela,user_id,name,amount_c,paid,ts) SELECT ?1,?2,?3,?4,?5,0,?6 WHERE EXISTS(SELECT 1 FROM picks WHERE round_id=?1 AND cartela=?2 AND user_id=?3)').bind(roundId, no, u.id, u.name, amount_c, Date.now()),
        db.prepare('UPDATE users SET balance=balance+?4 WHERE id=?3 AND EXISTS(SELECT 1 FROM bonus_wins WHERE round_id=?1 AND cartela=?2 AND user_id=?3 AND paid=0)').bind(roundId, no, u.id, amount_c),
        db.prepare('UPDATE bonus_wins SET paid=1 WHERE round_id=?1 AND cartela=?2 AND user_id=?3 AND paid=0').bind(roundId, no, u.id)]);
      return r[2].meta.changes > 0 ? { cartela: no, name: u.name, amount: B(amount_c) } : null;
    } catch (e) { }
  }
  return null;
}

/* ---------- shared game rounds (advanced only inside the GameHub Durable Object) ---------- */
const latest = db => db.prepare('SELECT * FROM rounds ORDER BY id DESC LIMIT 1').first();
const callsAt = (r, now) => Math.min(75, Math.max(0, Math.floor((now - r.start_ts - LOBBY_MS) / CALL_MS) + 1));
// Once a round has started its picks and number order never change, so they are kept in memory
// (one database read per round instead of one per request) and the winner check only looks at newly called numbers.
let rcache = null;
async function roundCache(env, r) {
  if (rcache && rcache.id === r.id) return rcache;
  const picks = (await env.DB.prepare('SELECT p.cartela,p.user_id,u.name FROM picks p JOIN users u ON u.id=p.user_id WHERE p.round_id=?').bind(r.id).all()).results;
  return rcache = { id: r.id, picks, order: numberOrder(r.seed), cards: null, k: 0, marked: new Set(), win: null, manual: new Set(), mt: 0 };
}
function winnersAt(rc, k) { // same result as findWinners(order, picks, k), but remembers how far it already checked
  if (!rc.cards) rc.cards = rc.picks.map(p => makeCard(p.cartela));
  while (!rc.win && rc.k < k) {
    rc.marked.add(rc.order[rc.k]); rc.k++;
    const w = rc.picks.filter((p, i) => !rc.manual.has(p.user_id) && hasBingo(rc.cards[i], rc.marked));
    if (w.length) rc.win = { k: rc.k, picks: w };
  }
  return rc.win;
}
function refundAndClose(env, r, from, now) {
  const db = env.DB;
  return db.batch([
    db.prepare("UPDATE users SET bonus_c=MIN(?5,bonus_c+(SELECT COALESCE(SUM(p.bonus_c),0) FROM picks p WHERE p.round_id=?1 AND p.user_id=users.id)),balance=balance+(SELECT COUNT(*)*?2-COALESCE(SUM(p.bonus_c),0) FROM picks p WHERE p.round_id=?1 AND p.user_id=users.id) WHERE id IN(SELECT user_id FROM picks WHERE round_id=?1) AND EXISTS(SELECT 1 FROM rounds WHERE id=?1 AND status=?4)").bind(r.id, r.stake_c, now, from, bonusC(env)),
    db.prepare("UPDATE rounds SET status='cancelled',ended_ts=?3 WHERE id=?1 AND status=?2").bind(r.id, from, now)]);
}
async function refreshManual(env, r, rc, now) { // players with Automatic switched off (re-read at most every 2 seconds)
  if (now - rc.mt < 2000) return; rc.mt = now;
  rc.manual = new Set((await env.DB.prepare('SELECT DISTINCT p.user_id FROM picks p JOIN users u ON u.id=p.user_id WHERE p.round_id=? AND u.auto_off=1').bind(r.id).all()).results.map(x => x.user_id));
}
let bgWait = null; // set by the GameHub: keeps a background promise alive (the winners' Telegram messages)
async function settle(env, r, picks, w, now) { // pays the winners and ends the round; returns false if another request already did
  await ensureTables(env);
  const db = env.DB, prize = Math.floor(picks.length * r.stake_c * CUT), share = Math.floor(prize / w.picks.length);
  let sup = 0; try { sup = Number(JSON.parse(await getSet(env, 'autotake') || '{}').uid) || 0 } catch (e) { } // the support account never appears in the weekly ranking
  const wc = await wkCfg(env), wkOn = wkRunning(wc, now); // games count for the weekly bonus ONLY while the admin has it switched ON
  const res = await db.batch([...w.picks.map(p => db.prepare("UPDATE users SET balance=balance+?3 WHERE id=?2 AND EXISTS(SELECT 1 FROM rounds WHERE id=?1 AND status='running')").bind(r.id, p.user_id, share)),
    // weekly ranking: every player of this round gets +1 game (only while the round is still 'running', so it can never count twice)
    ...(wkOn ? [db.prepare("INSERT INTO wk_games(week,user_id,games) SELECT ?2,user_id,1 FROM(SELECT DISTINCT user_id FROM picks WHERE round_id=?1 AND user_id<>?3) WHERE EXISTS(SELECT 1 FROM rounds WHERE id=?1 AND status='running') ON CONFLICT(week,user_id) DO UPDATE SET games=games+1").bind(r.id, wc.start, sup)] : []),
    db.prepare("UPDATE rounds SET status='ended',ended_ts=?2,called_n=?3,winners=?4 WHERE id=?1 AND status='running'").bind(r.id, now, w.k, JSON.stringify(w.picks.map(p => p.cartela)))]);
  const done = res[res.length - 1].meta.changes > 0;
  if (done) { // only the request that really ended the round gets here, so every winner receives the message exactly once
    const per = new Map(); for (const p of w.picks) per.set(p.user_id, (per.get(p.user_id) || 0) + share); // a player with two winning cartelas gets one message with the total
    // NOT awaited: the round-end screen must not wait for Telegram (the money is already paid above)
    const pm = Promise.all([...per].map(([id, c]) => tg(env, 'sendMessage', { chat_id: id, text: `ዙር ${r.id} አሸናፊ ሆነዋል ብር = ${B(c)}` }))).catch(() => { });
    if (bgWait) bgWait(pm);
  }
  return done;
}
/* ---------- AUTO-TAKE: the admin switches it ON and picks a number N. At the start of every round the server takes N random free cartelas
   for the SUPPORT account (settings.autotake = {on,n,uid}). They are paid like a normal player's cartelas (stake from the support balance) and
   if one of them wins, the prize goes to the support account. It repeats every round until the admin switches it OFF. ---------- */
let atDone = 0;
async function autoTake(env, r) {
  if (atDone === r.id) return;
  let cf = null; try { cf = JSON.parse(await getSet(env, 'autotake') || 'null') } catch (e) { }
  if (!cf || !cf.on || !(cf.n >= 1) || !(cf.uid > 0)) return;
  const db = env.DB, mk = await db.prepare("SELECT v FROM settings WHERE k='at_round'").first();
  if (mk && mk.v === String(r.id)) { atDone = r.id; return } // this round was already filled (e.g. the hub restarted)
  await db.prepare("INSERT INTO settings(k,v) VALUES('at_round',?1) ON CONFLICT(k) DO UPDATE SET v=excluded.v").bind(String(r.id)).run(); atDone = r.id;
  const taken = new Set((await db.prepare('SELECT cartela FROM picks WHERE round_id=?').bind(r.id).all()).results.map(x => x.cartela));
  const bc = await bonusFor(env, r.id); if (bc) for (const i of bc.items) taken.add(i.c); // never use a secret bonus cartela
  const free = []; for (let i = 1; i <= TOTAL; i++) if (!taken.has(i)) free.push(i);
  for (let i = free.length - 1; i > 0; i--) { const j = rnd32() % (i + 1);[free[i], free[j]] = [free[j], free[i]] } // random order, different every round
  let got = 0;
  for (const no of free) {
    if (got >= cf.n) break;
    try {
      const res = await db.batch([
        db.prepare("INSERT INTO picks(round_id,cartela,user_id,bonus_c) SELECT ?1,?2,?3,0 WHERE (SELECT balance FROM users WHERE id=?3)>=?4 AND EXISTS(SELECT 1 FROM rounds WHERE id=?1 AND status='lobby')").bind(r.id, no, cf.uid, r.stake_c),
        db.prepare("UPDATE users SET balance=balance-?4 WHERE id=?3 AND EXISTS(SELECT 1 FROM picks WHERE round_id=?1 AND cartela=?2 AND user_id=?3)").bind(r.id, no, cf.uid, r.stake_c)]);
      if (res[0].meta.changes === 0) break; // the support balance is too low for one more stake
      got++;
    } catch (e) { } // somebody took this cartela a moment ago: try the next one
  }
}
async function advance(env) {
  const db = env.DB, now = Date.now(); let r = await latest(db);
  if (!r || (r.status !== 'lobby' && r.status !== 'running' && now - r.ended_ts >= REST_MS)) {
    if (!r || (await getSet(env, 'paused')) !== '1') { // admin can pause new rounds
      await db.prepare("INSERT INTO rounds(start_ts,seed,status,stake_c) SELECT ?1,?2,'lobby',?3 WHERE NOT EXISTS(SELECT 1 FROM rounds WHERE status IN('lobby','running'))").bind(now, rnd32(), C((await getSet(env, 'stake')) || env.STAKE || 10)).run();
      r = await latest(db);
    }
  }
  if (r && r.status === 'lobby' && now - r.start_ts < LOBBY_MS) { try { await autoTake(env, r) } catch (e) { } } // admin auto-take for the support account
  if (r.status === 'lobby' && now - r.start_ts >= LOBBY_MS) {
    let at = {}; try { at = JSON.parse(await getSet(env, 'autotake') || '{}') || {} } catch (e) { }
    const pc = await db.prepare('SELECT COUNT(DISTINCT user_id) n,COALESCE(SUM(CASE WHEN user_id=?2 THEN 1 ELSE 0 END),0) s FROM picks WHERE round_id=?1').bind(r.id, Number(at.uid) || 0).first();
    const solo = !!(at.on && at.uid > 0 && pc.n === 1 && pc.s > 0); // AutoTake ON: the support account's cartelas may play alone, round after round, until it is switched OFF
    if (pc.n < 2 && !solo) await refundAndClose(env, r, 'lobby', now); // otherwise a game needs at least 2 players
    else await db.prepare("UPDATE rounds SET status='running' WHERE id=?1 AND status='lobby'").bind(r.id).run();
    r = await db.prepare('SELECT * FROM rounds WHERE id=?').bind(r.id).first();
  }
  if (r.status === 'running') {
    const k = callsAt(r, now), rc = await roundCache(env, r), picks = rc.picks;
    await refreshManual(env, r, rc, now);
    const w = winnersAt(rc, k);
    if (w) {
      await settle(env, r, picks, w, now);
    } else if (k >= 75) await refundAndClose(env, r, 'running', now);
    r = await db.prepare('SELECT * FROM rounds WHERE id=?').bind(r.id).first();
  }
  return r;
}

/* ---------- broadcast helper (used by the "bc" GameHub instance) ---------- */
async function bcSend(env, id, text) { // one message with the play button; waits and retries once when Telegram says "too many requests"
  const useP = env.PROMO_PHOTO && text.length <= 1000, kb = { inline_keyboard: playKb(env) };
  for (let t = 0; t < 2; t++) {
    const r = await (useP ? tg(env, 'sendPhoto', { chat_id: id, photo: env.PROMO_PHOTO, caption: text, reply_markup: kb }) : tg(env, 'sendMessage', { chat_id: id, text, reply_markup: kb }));
    if (!r) return false;
    if (r.status === 429) { let w = 3; try { w = (await r.json()).parameters.retry_after || 3 } catch (e) { } await sleep(Math.min(30, w) * 1000); continue }
    return r.ok;
  }
  return false;
}

/* ---------- GameHub: ONE Durable Object that holds the live game in memory ----------
   Every player poll is answered from memory. The database is touched only when something really changes:
   a round starts / ends, a number is called, a player picks or drops a cartela, or money moves.
   All the truth is still in D1, so if this object is ever restarted it rebuilds itself from the database.
   The same class is also used by a second instance named "bc" that only runs the broadcast (alarm). */
export class GameHub extends DurableObject {
  constructor(ctx, env) {
    super(ctx, env);
    bgWait = p => { try { ctx.waitUntil(p) } catch (e) { } };
    this.round = null; this.picks = []; this.pickRound = 0; this.pv = 0; this.pt = 0; this.nextAt = 0; this.busy = null; this.sh = null; this.lastOk = 0;
    this.bn = null; this.bv = 0; // bonus info for the open lobby: { round, locked, wins:[{cartela,name,amount}] }  (the secret cartelas are NOT kept here)
    this.bcfg = null; // the secret bonus setting for the open lobby (kept only in this object's memory)
  }
  async sync() { // returns the current round; asks the database only when the next event is due
    const now = Date.now();
    if (this.round && now < this.nextAt && !(this.round.status === 'lobby' && now - this.pt > 20000)) return this.round;
    if (!this.busy) this.busy = this.refresh().then(() => { this.lastOk = Date.now() }).catch(e => { // a short database hiccup: keep the last known round for up to 15 s instead of failing every player
      this.nextAt = Date.now() + 500; if (!this.round || Date.now() - this.lastOk > 15000) throw e;
    }).finally(() => { this.busy = null });
    await this.busy; return this.round;
  }
  async refresh() {
    const env = this.env, r = await advance(env), now = Date.now();
    if (r.status === 'lobby') {
      if (this.pickRound !== r.id || now - this.pt > 20000) await this.loadLobby(r);
    } else {
      const rc = await roundCache(env, r);
      if (this.picks !== rc.picks) { this.picks = rc.picks; this.pv++ }
      this.pickRound = r.id;
    }
    const k = r.status === 'running' ? callsAt(r, now) : 0;
    const due = r.status === 'lobby' ? r.start_ts + LOBBY_MS : r.status === 'running' ? r.start_ts + LOBBY_MS + k * CALL_MS : r.ended_ts + REST_MS;
    this.nextAt = Math.max(due, now + (r.status === 'running' ? 250 : 1000));
    this.round = r;
  }
  async loadLobby(r) {
    const v = this.pv;
    const rows = (await this.env.DB.prepare('SELECT p.cartela,p.user_id,u.name FROM picks p JOIN users u ON u.id=p.user_id WHERE p.round_id=?').bind(r.id).all()).results;
    if (this.pickRound !== r.id || v === this.pv) { this.picks = rows; this.pickRound = r.id; this.pv++ } // a pick that arrived while reading wins over the older read
    this.pt = Date.now();
    await this.loadBonus(r);
  }
  async loadBonus(r) { // is this round a bonus round (locked picks) and who has already won
    try {
      const cf = await bonusFor(this.env, r.id);
      const wins = (await this.env.DB.prepare('SELECT cartela,name,amount_c FROM bonus_wins WHERE round_id=? ORDER BY ts').bind(r.id).all()).results;
      this.bcfg = cf;
      this.bn = { round: r.id, locked: !!cf, wins: wins.map(w => ({ cartela: w.cartela, name: w.name, amount: B(w.amount_c) })) }; this.bv++;
    } catch (e) { this.pt = 0 } // could not read it: try again on the next request
  }
  async bonusCfg(roundId) { await this.sync(); return this.bcfg && this.bcfg.round === roundId ? this.bcfg : null } // secret bonus of this round (null = normal round); used by /api/pick
  async current() { return this.sync() } // the current round row, kept fresh
  async state(me) { // same JSON the old stateFor produced; me = { id, auto_off, balance, bonus_c } read fresh by the caller
    const r = await this.sync(), now = Date.now();
    const n = r.status === 'running' ? callsAt(r, now) : r.status === 'ended' ? r.called_n : 0;
    const key = r.id + '|' + r.status + '|' + this.pv + '|' + n + '|' + this.bv;
    let sh = this.sh;
    if (!sh || sh.key !== key) {
      const picks = this.picks, by = new Map();
      for (const p of picks) { let a = by.get(p.user_id); if (!a) by.set(p.user_id, a = []); a.push(p.cartela) }
      const win = r.status === 'ended' ? JSON.parse(r.winners || '[]') : [];
      const called = n ? (await roundCache(this.env, r)).order.slice(0, n) : [];
      const bn = r.status === 'lobby' && this.bn && this.bn.round === r.id ? this.bn : null; // the bonus winner stays on screen only until the game starts
      sh = this.sh = { key, by, called, taken: picks.map(p => p.cartela), players: by.size, cards: picks.length,
        bround: bn ? { locked: bn.locked, wins: bn.wins.slice() } : { locked: false, wins: [] },
        derash: B(Math.floor(picks.length * r.stake_c * CUT)), winners: picks.filter(p => win.includes(p.cartela)).map(p => ({ cartela: p.cartela, name: p.name })) };
    }
    return { now, round: { id: r.id, status: r.status, start_ts: r.start_ts, lobby_ms: LOBBY_MS, call_ms: CALL_MS, stake: B(r.stake_c), rest_ms: REST_MS, ended_ts: r.ended_ts },
      taken: sh.taken, mine: sh.by.get(me.id) || [], called: sh.called, players: sh.players, cards: sh.cards,
      auto: !me.auto_off, derash: sh.derash, winners: sh.winners, bround: sh.bround, balance: B(me.balance), bonus: B(me.bonus_c) };
  }
  async picked(op, roundId, no, uid, name, me, win) { // the database already accepted this pick / unpick: update memory and answer
    if (this.round && this.round.id === roundId && this.round.status === 'lobby' && this.pickRound === roundId) {
      if (op === 'pick') { if (!this.picks.some(p => p.cartela === no)) this.picks.push({ cartela: no, user_id: uid, name }) }
      else this.picks = this.picks.filter(p => !(p.cartela === no && p.user_id === uid));
      if (win) { // this pick hit a bonus cartela: announce it to everybody right now
        if (!this.bn || this.bn.round !== roundId) this.bn = { round: roundId, locked: true, wins: [] };
        if (!this.bn.wins.some(w => w.cartela === win.cartela)) this.bn.wins.push(win);
        this.bv++;
      }
      this.pv++;
    }
    return this.state(me);
  }
  async bingo(me) { // manual BINGO button: wins only if one of your cartelas really is complete right now
    const r = await this.sync(), now = Date.now();
    if (r.status === 'ended' || r.status === 'cancelled') return { error: 'round_over' };
    if (r.status !== 'running') return { error: 'no_bingo' };
    const rc = await roundCache(this.env, r), k = callsAt(r, now), marked = new Set(rc.order.slice(0, k));
    const mine = rc.picks.filter(x => x.user_id === me.id && hasBingo(makeCard(x.cartela), marked));
    if (!mine.length) return { error: 'no_bingo' };
    if (!(await settle(this.env, r, rc.picks, { k, picks: mine }, now))) return { error: 'round_over' };
    this.nextAt = 0;
    const f = await this.env.DB.prepare('SELECT balance,bonus_c,auto_off FROM users WHERE id=?').bind(me.id).first();
    return { state: await this.state({ id: me.id, auto_off: f.auto_off, balance: f.balance, bonus_c: f.bonus_c }) };
  }
  async manualChanged() { if (rcache) rcache.mt = 0; this.nextAt = 0 } // a player switched Automatic on/off
  async invalidate() { this.nextAt = 0; this.pt = 0; cfg.t = 0 } // admin changed something: re-read (including the bonus) on the next request

  /* ----- broadcast to ALL players (runs only in the "bc" instance, one alarm = up to 250 players, about 25 messages per second) ----- */
  async bcStart(job) {
    const st = this.ctx.storage, cur = await st.get('bc');
    if (cur && !cur.done) return { error: 'running', sent: cur.sent, total: cur.total };
    const total = (await this.env.DB.prepare('SELECT COUNT(*) c FROM users WHERE phone IS NOT NULL').first()).c;
    await st.put('bc', { text: job.text, chat: job.chat, cursor: 0, sent: 0, fail: 0, total, done: false, ts: Date.now() });
    await st.setAlarm(Date.now() + 50);
    return { ok: true, total };
  }
  async bcStatus() { return (await this.ctx.storage.get('bc')) || null }
  async bcStop() {
    const st = this.ctx.storage, j = await st.get('bc'); if (!j || j.done) return false;
    j.done = true; j.stopped = true; await st.put('bc', j); try { await st.deleteAlarm() } catch (e) { } return true;
  }
  async alarm() {
    const env = this.env, st = this.ctx.storage, j = await st.get('bc'); if (!j || j.done) return;
    try {
      const rows = (await env.DB.prepare('SELECT id FROM users WHERE phone IS NOT NULL AND id>? ORDER BY id LIMIT 250').bind(j.cursor).all()).results;
      if (!rows.length) {
        j.done = true; await st.put('bc', j);
        await tg(env, 'sendMessage', { chat_id: j.chat, text: `✅ ማሰራጨት ተጠናቅቋል።\n📤 ተልኳል: ${j.sent}\n⚠️ አልደረሰም (ቦቱን ያገዱ): ${j.fail}\n👥 ጠቅላላ: ${j.total}` });
        return;
      }
      for (let i = 0; i < rows.length; i += 25) {
        const cur = await st.get('bc'); if (!cur || cur.done) return; // stopped by /stopbroadcast
        const t0 = Date.now(), g = rows.slice(i, i + 25), rs = await Promise.all(g.map(r => bcSend(env, r.id, j.text)));
        for (const ok of rs) ok ? j.sent++ : j.fail++;
        j.cursor = g[g.length - 1].id; await st.put('bc', j);
        const w = 1050 - (Date.now() - t0); if (w > 0) await sleep(w); // Telegram's safe speed: about 25 messages per second
      }
      await st.setAlarm(Date.now() + 100);
    } catch (e) { await st.setAlarm(Date.now() + 5000) }
  }
}
const hubOf = env => env.HUB.get(env.HUB.idFromName('main'));
const bcOf = env => env.HUB.get(env.HUB.idFromName('bc')); // separate instance: the broadcast never slows the game
const noHub = () => J({ error: 'server_error', detail: 'HUB binding is missing in wrangler.json' }, 500);
const poke = env => env.HUB ? hubOf(env).invalidate().catch(() => { }) : null;

const startOfDay = () => Math.floor((Date.now() + 3 * 36e5) / 864e5) * 864e5 - 3 * 36e5; // Ethiopia time (UTC+3)

/* ---------- weekly bonus: top players ranked by games played while the admin has the weekly bonus ON ----------
   Games are counted in wk_games when a round ends (see settle). Prizes are set by the admin (Admin > Weekly) and paid by the admin with one button after the period is over. */
const maskPhone = p => p ? String(p).slice(0, 3) + '****' + String(p).slice(-2) : '';
const prizesOf = async env => { try { const a = JSON.parse(await getSet(env, 'wk_prizes') || '[]'); return Array.isArray(a) ? a.slice(0, 10).map(x => Math.max(0, Number(x) || 0)) : [] } catch (e) { return [] } };
const wkTop = (env, wk, n) => env.DB.prepare('SELECT g.user_id id,u.name n,u.phone ph,g.games g FROM wk_games g JOIN users u ON u.id=g.user_id WHERE g.week=?1 ORDER BY g.games DESC,g.user_id LIMIT ?2').bind(wk, n).all().then(r => r.results);
const wkRows = (top, pr) => top.map((x, i) => ({ rank: i + 1, name: x.n, phone: maskPhone(x.ph), games: x.g, prize: pr[i] || 0 }));
let wkCache = { w: 0, t: 0, top: [] }; // the top 10 is cached for 15 seconds so opening the Scores tab is cheap
async function weeklyBoard(env, u) {
  await ensureTables(env);
  const db = env.DB, now = Date.now(), wc = await wkCfg(env), run = wkRunning(wc, now), wk = wc.start, pr = await prizesOf(env);
  let mg = 0, rank = null;
  if (run) {
    if (wkCache.w !== wk || now - wkCache.t > 15000) wkCache = { w: wk, t: now, top: await wkTop(env, wk, 10) };
    const mine = await db.prepare('SELECT games g FROM wk_games WHERE week=?1 AND user_id=?2').bind(wk, u.id).first(); mg = mine ? mine.g : 0;
    const higher = mg ? (await db.prepare('SELECT COUNT(*) c FROM wk_games WHERE week=?1 AND (games>?2 OR (games=?2 AND user_id<?3))').bind(wk, mg, u.id).first()).c : 0;
    rank = mg ? higher + 1 : null;
  }
  const lp = await db.prepare('SELECT week,ts FROM wk_paid ORDER BY ts DESC LIMIT 1').first();
  let last = null, won = null;
  if (lp) {
    const w = (await db.prepare('SELECT pos,name,prize_c,games FROM wk_winners WHERE week=? ORDER BY pos').bind(lp.week).all()).results;
    last = { winners: w.map(x => ({ rank: x.pos, name: x.name, prize: B(x.prize_c), games: x.games })) };
    const mw = await db.prepare('SELECT pos,prize_c,games FROM wk_winners WHERE week=? AND user_id=?').bind(lp.week, u.id).first();
    if (mw && lp.ts > now - 7 * 864e5) won = { rank: mw.pos, prize: B(mw.prize_c), games: mw.games }; // shown as a congratulations card for 7 days
  }
  return { period: 'weekly', active: run, top: run ? wkRows(wkCache.top, pr) : [], me: { rank, played: mg, prize: rank && rank <= 10 ? pr[rank - 1] || 0 : 0 }, ends_ts: run ? wc.end : 0, now, prizes_on: pr.some(x => x > 0), last, won };
}
async function leaderboard(env, u, period) {
  if (period === 'weekly') return weeklyBoard(env, u);
  const db = env.DB, since = startOfDay();
  const base = "FROM picks p JOIN rounds r ON r.id=p.round_id WHERE r.status='ended' AND r.ended_ts>=?1";
  const top = (await db.prepare(`SELECT u.name n,COUNT(DISTINCT p.round_id) g ${base.replace('WHERE', 'JOIN users u ON u.id=p.user_id WHERE')} GROUP BY u.id ORDER BY g DESC LIMIT 10`).bind(since).all()).results;
  const mine = (await db.prepare(`SELECT COUNT(DISTINCT p.round_id) g ${base} AND p.user_id=?2`).bind(since, u.id).first()).g || 0;
  const higher = (await db.prepare(`SELECT COUNT(*) c FROM(SELECT p.user_id,COUNT(DISTINCT p.round_id) g ${base} GROUP BY p.user_id HAVING g>?2)`).bind(since, mine).first()).c;
  return { period: 'daily', top: top.map(t => [t.n, t.g]), me: { rank: mine ? higher + 1 : null, played: mine } };
}

/* ---------- Telegram bot: menu buttons, deposit / withdraw / transfer flows, admin commands ---------- */
async function menuAction(env, u, act) { // a menu button was pressed
  const uid = u.id, db = env.DB;
  if (act === 'bal') { const f = await db.prepare('SELECT balance,bonus_c FROM users WHERE id=?').bind(uid).first(); return sendMenu(env, uid, `💳 ቀሪ ሂሳብዎ: ${B(f.balance)} ብር` + (f.bonus_c > 0 ? `\n🎁 ቦነስ: ${B(f.bonus_c)} ብር` : '')) }
  if (act === 'dep') { await setState(env, uid, 'dep_amount', {}); return sendTo(env, uid, `ማስገባት የፈለጉትን የብር መጠን ከ ${MIN_DEP} ብር ጀምሮ ያስገቡ።`) }
  if (act === 'ins') return sendMenu(env, uid, instructionText);
  if (act === 'wd') {
    if (!(await hasDeposit(env, uid))) return sendMenu(env, uid, '⚠️ ገንዘብ ለማውጣት ቢያንስ አንድ ጊዜ ገንዘብ ማስገባት ያስፈልጋል።');
    await setState(env, uid, 'wd_amount', {}); return sendTo(env, uid, `💸 ማውጣት የፈለጉትን የብር መጠን ከ ${MIN_WD} ብር ጀምሮ ያስገቡ።\n💳 ቀሪ ሂሳብዎ: ${B(u.balance)} ብር`);
  }
  if (act === 'tr') {
    if (!(await hasDeposit(env, uid))) return sendMenu(env, uid, '⚠️ ገንዘብ ለማስተላለፍ ቢያንስ አንድ ጊዜ ገንዘብ ማስገባት ያስፈልጋል።');
    await setState(env, uid, 'tr_phone', {}); return sendTo(env, uid, '🎁 ገንዘብ የሚልኩለትን ተጫዋች ስልክ ቁጥር ያስገቡ (ለምሳሌ 09xxxxxxxx)።');
  }
  if (act === 'inv') {
    const c = (await db.prepare('SELECT COUNT(*) c FROM referrals r JOIN users x ON x.id=r.user_id WHERE r.ref_id=? AND x.phone IS NOT NULL').bind(uid).first()).c;
    return sendMenu(env, uid, `🔗 ጓደኞችዎን ይጋብዙ!\n\nየእርስዎ መጋበዣ ሊንክ፦\nhttps://t.me/${env.BOT_USERNAME || ''}?start=ref${uid}\n\n👥 የተመዘገቡ ጓደኞችዎ፦ ${c}`);
  }
}
async function onPlayerCb(env, q, parts) { // menu / bank / cancel buttons
  const uid = q.from.id, a = parts[0];
  await tg(env, 'answerCallbackQuery', { callback_query_id: q.id });
  const u = await env.DB.prepare('SELECT * FROM users WHERE id=?').bind(uid).first();
  if (!u || !u.phone) return askContact(env, uid);
  if (await isBanned(env, uid)) return sendTo(env, uid, `⛔ አካውንትዎ ታግዷል። ለእርዳታ ${SUPPORT} ያነጋግሩ።`);
  if (a === 'm') { await clearState(env, uid); return menuAction(env, u, parts[1]) }
  if (a === 'b') {
    if (parts[1] === 'x') { await clearState(env, uid); return sendMenu(env, uid, '❌ ተሰርዟል።') }
    const flow = parts[1], bank = parts[2], st = await getState(env, uid);
    if (!(flow === 'w' ? WD_BANKS[bank] : BANKS[bank])) return;
    if (flow === 'd') {
      if (!st || st.step !== 'dep_bank') return sendMenu(env, uid, '⌛ ጊዜው አልፏል። እባክዎ «ገንዘብ አስገባ» ን እንደገና ይጫኑ።');
      await setState(env, uid, 'dep_paste', { amt: st.amt, method: bank });
      const dtxt = `የሚያጋጥማቹ የክፍያ ችግር:\n${SUPPORT} ላይ ፃፉልን።\n\n1. ከታች ባለው አካውንት ${st.amt} ብር ያስገቡ\n${acctText(env, bank)}\n\n2. የከፈሉበትን አጭር የጽሁፍ መልዕክት (SMS) ኮፒ በማድረግ እዚህ ላይ ፔስት (Paste) አድርገው ያስገቡና ይላኩት 👇👇👇\n\n⚠️ መልዕክቱን ሙሉ በሙሉ ያለምንም ለውጥ ይላኩ (የግብይት ቁጥሩን ጨምሮ)።`;
      const kc = copyKb(env, bank, st.amt), im = (await env.DB.prepare('SELECT data FROM account_imgs WHERE bank=?').bind(bank).first().catch(() => null)) || (IMG_DEF[bank] ? { data: IMG_DEF[bank] } : null); // if the admin saved a picture for this account it is sent with the instructions
      let rr = im && dtxt.length <= 1000 ? await sendPhotoData(env, uid, im.data, dtxt, kc) : null; if (!(rr && rr.ok)) rr = kc ? await tg(env, 'sendMessage', { chat_id: uid, text: dtxt, reply_markup: kc }) : null;
      return rr && rr.ok ? rr : sendTo(env, uid, dtxt);
    }
    if (flow === 'w') {
      if (!st || st.step !== 'wd_bank') return sendMenu(env, uid, '⌛ ጊዜው አልፏል። እባክዎ «አውጣ» ን እንደገና ይጫኑ።');
      await setState(env, uid, 'wd_account', { amt: st.amt, method: bank });
      return sendTo(env, uid, `${WD_BANKS[bank]} — ገንዘቡ የሚላክበትን አካውንት ወይም ስልክ ቁጥር ያስገቡ።`);
    }
  }
}
async function onStep(env, u, st, text) { // the player typed something while in a flow
  const uid = u.id, t = String(text).trim(), num = Number(t.replace(/,/g, '')), isAmt = t !== '' && isFinite(num) && num > 0 && num <= 100000;
  if (st.step === 'dep_amount') {
    if (!isAmt || num < MIN_DEP) return sendTo(env, uid, `⚠️ ማስገባት የሚችሉት ከ ${MIN_DEP} ብር ጀምሮ ነው። ቁጥር ብቻ ያስገቡ።`);
    await setState(env, uid, 'dep_bank', { amt: num });
    return sendTo(env, uid, '🏦 የሚፈልጉትን የክፍያ አማራጭ ይምረጡ፦\n- ከቴሌ ብር ወደ ቴሌ ብር\n- ከባንክ ወደ ተመሳሳይ ባንክ ብቻ ያስገቡ', bankKb(env, 'd'));
  }
  if (st.step === 'dep_bank') return sendTo(env, uid, '👇 እባክዎ ከታች ካሉት አማራጮች ይምረጡ።', bankKb(env, 'd'));
  if (st.step === 'dep_paste') {
    const pr = parsePaste(t);
    if (!pr) return sendTo(env, uid, '⚠️ የግብይት ቁጥር አልተገኘም። የከፈሉበትን ሙሉ መልዕክት እንደገና ኮፒ አድርገው ፔስት ያድርጉ።');
    const amt = pr.amount_c ? B(pr.amount_c) : st.amt; // the amount written in the bank SMS is the real money, so it wins over the typed amount
    if (amt < MIN_DEP) return sendTo(env, uid, `⚠️ ማስገባት የሚችሉት ከ ${MIN_DEP} ብር ጀምሮ ነው። በመልዕክቱ ላይ ያለው መጠን ${amt} ብር ነው።`);
    const method = st.method === 'mpesa' || st.method === 'ebirr' ? st.method : (pr.bank || st.method); // M-Pesa / E-birr are recorded as chosen by the player
    const r = await makeDeposit(env, u, amt, pr.txid, method);
    if (r.error === 'too_many_pending') { await clearState(env, uid); return sendMenu(env, uid, '⚠️ ብዙ ያልተረጋገጡ የገቢ ጥያቄዎች አሉዎት። እስኪረጋገጡ ይጠብቁ ወይም ' + SUPPORT + ' ያነጋግሩ።') }
    if (r.error) return sendTo(env, uid, '⚠️ ይህ የግብይት ቁጥር ከዚህ በፊት ተመዝግቧል። ሌላ መልዕክት ያስገቡ።');
    await clearState(env, uid);
    return r.status === 'approved' ? null : sendMenu(env, uid, r.held ? `⏳ የ${amt} ብር ጥያቄዎ ደርሶናል። አስተዳዳሪው እያረጋገጠ ነው፣ ጥቂት ይጠብቁ።` : `⏳ የ${amt} ብር ጥያቄዎ ደርሶናል። መልዕክቱ ሲረጋገጥ ገንዘቡ በራስ-ሰር ወደ ሂሳብዎ ይጨመራል (አስተዳዳሪውም ያረጋግጣል)።`);
  }
  if (st.step === 'wd_amount') {
    if (!isAmt || num < MIN_WD) return sendTo(env, uid, `⚠️ ማውጣት የሚችሉት ከ ${MIN_WD} ብር ጀምሮ ነው። ቁጥር ብቻ ያስገቡ።`);
    if (C(num) > u.balance) return sendTo(env, uid, `⚠️ ቀሪ ሂሳብዎ በቂ አይደለም (${B(u.balance)} ብር)። ሌላ መጠን ያስገቡ።`);
    await setState(env, uid, 'wd_bank', { amt: num });
    return sendTo(env, uid, '🏦 ገንዘቡ የሚላክበትን አማራጭ ይምረጡ፦', bankKb(env, 'w'));
  }
  if (st.step === 'wd_bank') return sendTo(env, uid, '👇 እባክዎ ከታች ካሉት አማራጮች ይምረጡ።', bankKb(env, 'w'));
  if (st.step === 'wd_account') {
    const account = t.slice(0, 40); if (account.length < 4) return sendTo(env, uid, '⚠️ አካውንት ወይም ስልክ ቁጥር በትክክል ያስገቡ።');
    const r = await makeWithdrawal(env, u, st.amt, account, st.method);
    if (r.error === 'deposit_required') { await clearState(env, uid); return sendMenu(env, uid, '⚠️ ገንዘብ ለማውጣት ቢያንስ አንድ ጊዜ ገንዘብ ማስገባት ያስፈልጋል።') }
    if (r.error) { await clearState(env, uid); return sendMenu(env, uid, '⚠️ ቀሪ ሂሳብዎ በቂ አይደለም።') }
    await clearState(env, uid);
    return sendMenu(env, uid, `✅ የ${st.amt} ብር የማውጣት ጥያቄዎ ተልኳል። አስተዳዳሪው ሲልክልዎ መልዕክት ይደርስዎታል።`);
  }
  if (st.step === 'tr_phone') {
    const ph = normPhone(t); if (!ph) return sendTo(env, uid, '⚠️ ስልክ ቁጥሩ ትክክል አይደለም። (09… ወይም 07…) ያስገቡ።');
    const to = await env.DB.prepare('SELECT id,name FROM users WHERE phone=?').bind(ph).first();
    if (!to) return sendTo(env, uid, '⚠️ በዚህ ስልክ ቁጥር የተመዘገበ ተጫዋች አልተገኘም።');
    if (to.id === uid) return sendTo(env, uid, '⚠️ ለራስዎ ማስተላለፍ አይችሉም።');
    await setState(env, uid, 'tr_amount', { to: to.id, name: to.name });
    return sendTo(env, uid, `🎁 ለ ${to.name} የሚልኩትን የብር መጠን ያስገቡ (ከ ${MIN_TR} ብር ጀምሮ)።\n💳 ቀሪ ሂሳብዎ: ${B(u.balance)} ብር`);
  }
  if (st.step === 'tr_amount') {
    if (!isAmt || num < MIN_TR) return sendTo(env, uid, `⚠️ ማስተላለፍ የሚችሉት ከ ${MIN_TR} ብር ጀምሮ ነው። ቁጥር ብቻ ያስገቡ።`);
    const r = await makeTransfer(env, u, st.to, num);
    await clearState(env, uid);
    if (r.error) return sendMenu(env, uid, '⚠️ ቀሪ ሂሳብዎ በቂ አይደለም።');
    await say(env, st.to, `🎁 ${num} ብር ከ ${u.name} ተላልፎልዎታል።`, playKb(env));
    return sendMenu(env, uid, `✅ ${num} ብር ለ ${st.name} ተልኳል።`);
  }
  return null;
}

async function onTelegram(env, up) {
  const db = env.DB; await ensureTables(env); await loadAcc(env);
  if (up.callback_query) {
    const q = up.callback_query, parts = String(q.data).split(':'), [a, id] = parts;
    if (a === 'm' || a === 'b') return onPlayerCb(env, q, parts);
    if (!(await isAdmin(env, q.from.id))) return tg(env, 'answerCallbackQuery', { callback_query_id: q.id, text: 'ለአስተዳዳሪ ብቻ' });
    if (a === 'dv') { const r = await recheckDeposit(env, +id); return tg(env, 'answerCallbackQuery', { callback_query_id: q.id, text: r.text.slice(0, 190), show_alert: true }) } // "🔎 verify.et" button: check this pending deposit again
    if (a === 'da' && !manualDep(env) && !(await heldById(env, +id))) return tg(env, 'answerCallbackQuery', { callback_query_id: q.id, text: '🔒 ይህ ገቢ በእጅ እንዲጸድቅ አልተከፈተም (ወይም ቀድሞ ተከናውኗል) — ገቢው በSMS ወይም በverify.et ሲረጋገጥ ይጨመራል።', show_alert: true });
    const ok = a === 'da' ? await decideDeposit(env, +id, true, true) : a === 'dr' ? await decideDeposit(env, +id, false) : a === 'wp' ? await decideWithdraw(env, +id, true) : a === 'wr' ? await decideWithdraw(env, +id, false) : false;
    await tg(env, 'answerCallbackQuery', { callback_query_id: q.id, text: ok ? 'ተጠናቋል' : 'ቀድሞ ተከናውኗል' });
    return tg(env, 'editMessageText', { chat_id: q.message.chat.id, message_id: q.message.message_id, text: q.message.text + (ok ? '\n\n✔ ተጠናቋል' : '\n\n(ቀድሞ ተከናውኗል)') });
  }
  const m = up.message; if (!m) return;
  if (m.contact) return onContact(env, m); // player shared their phone number
  if (!m.text) return;
  const text0 = m.text.trim(), text = LEG[text0] || text0, cmd = text.split(/[\s@]/)[0].toLowerCase(), uid = m.from.id; await refreshBonus(env, uid, Date.now()); const u = await db.prepare('SELECT * FROM users WHERE id=?').bind(uid).first(); // an old English keyboard button is read as its Amharic twin
  if (text.startsWith('/') || isBtn(text) || text === 'Admin 🛠') await clearState(env, uid); // a command or menu text always leaves any flow
  if (cmd === '/start' && !(u && u.phone)) { // remember who invited this player
    const mm = text.match(/^\/start(?:@\w+)?\s+ref(\d+)/i);
    if (mm && Number(mm[1]) !== uid) await db.prepare('INSERT OR IGNORE INTO referrals(user_id,ref_id,ts) VALUES(?,?,?)').bind(uid, Number(mm[1]), Date.now()).run();
  }
  if (cmd === '/balance' || text === BTN.bal || text === BOT.bal) {
    if (!u || !u.phone) return askContact(env, uid);
    return menuAction(env, u, 'bal');
  }
  if (isOwner(env, uid) && (cmd === '/addadmin' || cmd === '/removeadmin' || cmd === '/admins')) {
    const list = await admins(env), id = (m.text.split(/\s+/)[1] || '').replace(/\D/g, '');
    if (cmd === '/admins') return say(env, uid, 'አስተዳዳሪዎች፦\n' + list.join('\n'));
    if (!id) return say(env, uid, 'እንዲህ ይላኩ፦ ' + cmd + ' 123456789');
    if (cmd === '/addadmin') { await db.prepare('INSERT OR IGNORE INTO admins(id,added_ts) VALUES(?,?)').bind(Number(id), Date.now()).run(); admCache.t = 0; await say(env, id, 'አሁን አስተዳዳሪ ሆነዋል። ዳሽቦርዱን ለመክፈት /admin ይላኩ።'); return say(env, uid, '✅ አስተዳዳሪ ተጨምሯል ' + id) }
    if (isOwner(env, id)) return say(env, uid, 'ባለቤቶች በCloudflare ብቻ ይቀየራሉ።');
    await db.prepare('DELETE FROM admins WHERE id=?').bind(Number(id)).run(); admCache.t = 0; return say(env, uid, '✅ አስተዳዳሪ ተወግዷል ' + id);
  }
  if (cmd === '/pending' && await isAdmin(env, uid)) {
    const d = (await db.prepare("SELECT d.*,u.name,u.phone FROM deposits d JOIN users u ON u.id=d.user_id WHERE d.status='pending'").all()).results, w = (await db.prepare("SELECT w.*,u.name,u.phone FROM withdrawals w JOIN users u ON u.id=w.user_id WHERE w.status='pending'").all()).results;
    if (!d.length && !w.length) return say(env, uid, 'በመጠባበቅ ላይ ያለ ምንም ጥያቄ የለም ✅');
    for (const x of d) { const h = await isHeld(env, x.txid); await say(env, uid, depositText({ ...x, manual: (manualDep(env) || h) ? '1' : '', held: h ? 'hold' : '' }), depKb(env, x.id, x.method, h)) }
    for (const x of w) { x.info = await wdInfo(env, x.user_id).catch(() => ''); await say(env, uid, withdrawText(x), [[{ text: '💸 ተከፍሏል', callback_data: 'wp:' + x.id }, { text: '↩️ ውድቅ', callback_data: 'wr:' + x.id }]]) }
    return;
  }
  if ((cmd === '/admin' || text === 'Admin 🛠') && await isAdmin(env, uid)) return tg(env, 'sendMessage', { chat_id: uid, text: 'የአስተዳዳሪ ዳሽቦርድ', reply_markup: { inline_keyboard: [[{ text: 'አስተዳዳሪ ክፈት 🛠', web_app: { url: adminUrl(env) } }]] } });
  if (isOwner(env, uid) && (cmd === '/broadcast' || cmd === '/more' || cmd === '/stopbroadcast')) { // ONE command sends to ALL registered players, in the background
    if (!env.HUB) return say(env, uid, '⚠️ HUB binding is missing in wrangler.json');
    const bc = bcOf(env);
    if (cmd === '/stopbroadcast') return say(env, uid, (await bc.bcStop()) ? '⛔ ማሰራጨት ቆሟል።' : 'የሚሰራ ማሰራጨት የለም።');
    if (cmd === '/more') { // progress
      const s = await bc.bcStatus();
      if (!s) return say(env, uid, 'እስካሁን ምንም ማሰራጨት አልተጀመረም። ለመጀመር፦ /broadcast መልዕክትዎ');
      return say(env, uid, (s.done ? (s.stopped ? '⛔ ቆሟል' : '✅ ተጠናቅቋል') : '⏳ እየተላከ ነው') + `\n📤 ተልኳል: ${s.sent}\n⚠️ አልደረሰም: ${s.fail}\n👥 ጠቅላላ: ${s.total}`);
    }
    const t0 = m.text.replace(/^\/broadcast(@\w+)?\s*/i, '');
    if (!t0) return say(env, uid, 'እንዲህ ይላኩ፦ /broadcast መልዕክትዎ');
    const r = await bc.bcStart({ text: t0, chat: uid });
    if (r.error) return say(env, uid, `⏳ ማሰራጨት አሁን እየሰራ ነው (ተልኳል ${r.sent} ከ ${r.total})። ለማቆም /stopbroadcast ይላኩ።`);
    return say(env, uid, `📤 ማሰራጨት ተጀምሯል — ለሁሉም ${r.total} ተጫዋቾች በራስ-ሰር ይላካል (ወደ ${Math.max(1, Math.ceil(r.total / 25 / 60))} ደቂቃ ይፈጃል)። ሲጨርስ መልዕክት ይደርስዎታል።\nሂደቱን ለማየት /more · ለማቆም /stopbroadcast`);
  }
  if (isOwner(env, uid) && cmd === '/keyboard') { // pushes the bottom keyboard to every registered player, 40 at a time. Send /keyboard again for the next batch, "/keyboard reset" to start over.
    if (/reset/i.test(m.text)) await setSet(env, 'kb_cursor', '0');
    const cur = Number(((await db.prepare("SELECT v FROM settings WHERE k='kb_cursor'").first()) || {}).v || 0);
    const rows = (await db.prepare('SELECT id FROM users WHERE phone IS NOT NULL AND id>? ORDER BY id LIMIT 40').bind(cur).all()).results;
    if (!rows.length) return say(env, uid, '✅ ሁሉም ተጫዋች ቁልፎቹን አግኝቷል።');
    await Promise.all(rows.map(r => sendBottom(env, r.id, KBNOTE)));
    await setSet(env, 'kb_cursor', String(rows[rows.length - 1].id));
    return say(env, uid, `⌨️ ቁልፎቹ ለ${rows.length} ተጫዋቾች ተልከዋል። ቀጣዩን ለመላክ /keyboard እንደገና ይላኩ።`);
  }
  if (!u || !u.phone) return askContact(env, uid); // new player: must share the phone number first
  if (await isBanned(env, uid)) return sendTo(env, uid, `⛔ አካውንትዎ ታግዷል። ለእርዳታ ${SUPPORT} ያነጋግሩ።`);
  if (cmd === '/start') { await sendBottom(env, uid, '👋 ሰላም!\n\nለመጫወት ወይም ገንዘብ ለማስገባት ከታች ያሉትን ቁልፎች ይጫኑ።'); return sendMenu(env, uid, '🎮 ሌሎች አማራጮች ከታች አሉ።') } // shows the bottom keyboard + the inline menu
  if (!(await db.prepare('SELECT 1 x FROM kb_sent WHERE uid=?').bind(uid).first())) await sendBottom(env, uid, KBNOTE); // old players get the bottom keyboard once, on their next message
  const st = await getState(env, uid); if (st) { const h = await onStep(env, u, st, text); if (h !== null && h !== undefined) return h; if (st.step === 'dep_paste') return } // inside a flow: the step handles the message
  if (text === BTN.play || text === BOT.play || cmd === '/play') return sendTo(env, uid, '🎮 ለመጫወት ከታች ያለውን ቁልፍ ይጫኑ።', { inline_keyboard: playKb(env) });
  if (text === BTN.dep || text === BOT.dep || cmd === '/deposit') return menuAction(env, u, 'dep');
  if (text === BTN.sup || cmd === '/support') return sendTo(env, uid, `🆘 ለእርዳታ ያነጋግሩን: ${SUPPORT}`, { inline_keyboard: [[{ text: 'እርዳታ 🆘', url: 'https://t.me/' + SUPPORT.slice(1) }]] });
  if (cmd === '/withdraw') return menuAction(env, u, 'wd');
  if (cmd === '/transfer') return menuAction(env, u, 'tr');
  if (cmd === '/invite') return menuAction(env, u, 'inv');
  if (cmd === '/instruction') return menuAction(env, u, 'ins');
  return sendMenu(env, uid, '🎮 እንኳን ደህና መጡ! ከታች ካሉት አማራጮች ይምረጡ።');
}
const depositText = x => `💰 ገቢ #${x.id}\n${x.name} · ${x.phone}\nመጠን: ${B(x.amount_c)} ብር በ ${x.method}\nየግብይት ቁጥር: ${x.txid}\n` + (x.held ? 'ራስ-ሰር አልተጨመረም — ለእርስዎ ማረጋገጫ ተይዟል። ገንዘቡ በእርግጥ መድረሱን በባንክ አፕዎ ካረጋገጡ ብቻ ያጽድቁ።' : 'የሚዛመድ SMS ገና አልደረሰም — SMS ሲደርስ በራስ-ሰር ይጨመራል፤ ገንዘቡ በእርግጥ መድረሱን ካረጋገጡ ብቻ በእጅ ያጽድቁ።') + (manualDep({ ALLOW_MANUAL_DEPOSIT: x.manual }) || x.held ? '' : '\n\n🔒 በእጅ ማጽደቅ ተዘግቷል — ገቢው በSMS ወይም በverify.et ሲረጋገጥ ብቻ ይጨመራል።') + (x.flags ? '\n\n🔎 ምርመራ፦\n' + x.flags : '');
const notifyAdmins = async (env, text, kb) => Promise.all((await admins(env)).map(a => say(env, a, text, kb)));
const withdrawText = x => `💸 ወጪ #${x.id}\n${x.name} · ${x.phone}\nመጠን: ${B(x.amount_c)} ብር\nይላክ ወደ: ${x.method} ${x.account}` + (x.info ? '\n\n' + x.info : '');

/* ---------- admin dashboard routes (password = ADMIN_KEY secret, or a Telegram admin account) ---------- */
async function adminRoute(req, env, url) {
  const key = req.headers.get('x-admin-key');
  let actor = null;
  if (env.ADMIN_KEY && key === env.ADMIN_KEY) actor = 'password';
  else { const tu = await verifyInit(req.headers.get('x-init-data'), env.BOT_TOKEN); if (tu && await isAdmin(env, tu.id)) actor = String(tu.id); }
  if (!actor) return J({ error: 'forbidden' }, 403);
  await ensureTables(env);
  const db = env.DB, name = url.pathname.replace('/api/admin/', '');
  const b = req.method === 'POST' ? await req.json().catch(() => ({})) : {};
  const log = (action, detail) => db.prepare('INSERT INTO admin_log(ts,actor,action,detail) VALUES(?,?,?,?)').bind(Date.now(), actor, action, String(detail || '')).run();

  if (name === 'overview') { // ONE database round trip for all the numbers
    const o = await db.prepare(`SELECT (SELECT COUNT(*) FROM users) players,
      (SELECT COALESCE(SUM(amount_c),0) FROM deposits WHERE status='approved') dep,
      (SELECT COALESCE(SUM(amount_c),0) FROM deposits WHERE status='approved' AND ts>=?1) dep_t,
      (SELECT COUNT(*) FROM deposits WHERE status='approved' AND ts>=?1) dep_n,
      (SELECT COALESCE(SUM(amount_c),0) FROM withdrawals WHERE status='paid') wd,
      (SELECT COUNT(*) FROM deposits WHERE status='pending') pd,
      (SELECT COUNT(*) FROM withdrawals WHERE status='pending') pw,
      (SELECT COUNT(*) FROM rounds WHERE status='ended') rounds,
      (SELECT COALESCE(SUM(balance),0) FROM users) held`).bind(startOfDay()).first(); // today = since 00:00 Ethiopia time
    return J({ players: o.players, deposits: B(o.dep), deposits_today: B(o.dep_t), deposits_today_count: o.dep_n, withdrawals: B(o.wd), pending: o.pd + o.pw, rounds: o.rounds, held: B(o.held) });
  }
  if (name === 'deposits') { // last 100 credited deposits with the player name (Overview > tap "Deposits today (count)")
    const r = (await db.prepare("SELECT d.id,d.amount_c,d.method,d.note,d.ts,u.name,u.phone FROM deposits d JOIN users u ON u.id=d.user_id WHERE d.status='approved' ORDER BY d.id DESC LIMIT 100").all()).results;
    return J({ today_ts: startOfDay(), items: r.map(x => ({ id: x.id, name: x.name, phone: x.phone || '', amount: B(x.amount_c), method: x.method, how: x.note || '', ts: x.ts })) });
  }
  if (name === 'pending') { // the three lists are read at the same time, and each withdrawal's history too
    const [dr, wr, hr] = await Promise.all([
      db.prepare("SELECT d.id,d.amount_c,d.method,d.txid,u.name,u.phone,(SELECT amount_c FROM sms_log WHERE txid=d.txid) sms_c,(SELECT verdict||' · '||detail FROM verify_log WHERE txid=d.txid) vet FROM deposits d JOIN users u ON u.id=d.user_id WHERE d.status='pending' ORDER BY d.id").all(),
      db.prepare("SELECT w.id,w.user_id,w.amount_c,w.method,w.account,u.name,u.phone FROM withdrawals w JOIN users u ON u.id=w.user_id WHERE w.status='pending' ORDER BY w.id").all(),
      db.prepare("SELECT 'deposit' type,d.amount_c,d.method detail,d.status,d.ts,u.name,u.phone FROM deposits d JOIN users u ON u.id=d.user_id WHERE d.status IN('approved','rejected') AND d.ts>? UNION ALL SELECT 'withdraw',w.amount_c,w.method||' '||w.account,w.status,w.ts,u.name,u.phone FROM withdrawals w JOIN users u ON u.id=w.user_id WHERE w.status IN('paid','rejected') AND w.ts>? ORDER BY ts DESC LIMIT 60").bind(Date.now() - 864e5, Date.now() - 864e5).all().catch(() => ({ results: [] }))]);
    const d = dr.results, w = wr.results, hist = hr.results;
    await Promise.all(w.map(async x => { x.info = await wdInfo(env, x.user_id).catch(() => '') }));
    return J({ items: [
      ...d.map(x => ({ type: 'deposit', id: x.id, amount: B(x.amount_c), name: x.name, phone: x.phone, can_vet: !!(env.VERIFYET_KEY && VET_BANK[x.method]), manual: manualDep(env) || /^(bad|hold) /.test(x.vet || ''), detail: x.method + ' · tx ' + x.txid + (x.sms_c == null ? ' · ❌ no matching bank SMS yet' : x.sms_c !== x.amount_c ? ' · 🚨 real SMS says ' + B(x.sms_c) + ' birr (claimed ' + B(x.amount_c) + ')' : ' · ✅ SMS matches') + (x.vet ? ' · 🔎 ' + x.vet : '') })),
      ...w.map(x => ({ type: 'withdraw', id: x.id, amount: B(x.amount_c), name: x.name, phone: x.phone, detail: 'send to ' + x.method + ' ' + x.account + (x.info ? ' · ' + x.info.replace(/\n\s*/g, ' · ') : '') }))
    ], history: hist.map(h => ({ type: h.type, amount: B(h.amount_c), name: h.name, phone: h.phone, detail: h.detail, status: h.status, ts: h.ts })) });
  }
  if (name === 'recheck') { // "🔎 verify.et" button in Admin > Pending: check one pending deposit again
    const id = Math.floor(Number(b.id)); if (!(id > 0)) return J({ error: 'bad_input' }, 400);
    const r = await recheckDeposit(env, id); await log('verify.et recheck', 'deposit #' + id + ' · ' + (r.ok ? 'credited' : 'not credited'));
    return J(r);
  }
  if (name === 'approve' || name === 'reject') {
    const id = Math.floor(Number(b.id)); if (!(id > 0)) return J({ error: 'bad_input' }, 400);
    const ok = name === 'approve'; let done;
    if (ok && b.type === 'deposit' && !manualDep(env) && !(await heldById(env, id))) return J({ error: 'manual_off' }, 409); // only a HELD deposit may be approved by hand while manual approval is locked
    if (b.type === 'deposit') done = await decideDeposit(env, id, ok, true);
    else if (b.type === 'withdraw') done = await decideWithdraw(env, id, ok); // approve = mark paid, reject = refund balance
    else return J({ error: 'bad_input' }, 400);
    if (done) await log(name, b.type + ' #' + id);
    return J({ ok: done });
  }
  if (name === 'players') {
    const q = String(url.searchParams.get('q') || '').trim().slice(0, 40), like = '%' + q + '%';
    const sql = 'SELECT u.id,u.name,u.phone,u.balance,(SELECT 1 FROM bans WHERE id=u.id) banned FROM users u' + (q ? ' WHERE u.name LIKE ?1 OR u.phone LIKE ?1 OR CAST(u.id AS TEXT) LIKE ?1' : '') + ' ORDER BY u.created_ts DESC LIMIT 100';
    const r = (await (q ? db.prepare(sql).bind(like) : db.prepare(sql)).all()).results;
    return J({ items: r.map(x => ({ id: x.id, name: x.name, phone: x.phone || 'not registered', balance: B(x.balance), banned: !!x.banned })) });
  }
  if (name === 'adjust') { // add (+) or remove (-) birr on a player's balance
    const id = Math.floor(Number(b.id)), amt = Number(b.amount);
    if (!(id > 0) || !isFinite(amt) || amt === 0 || Math.abs(amt) > 100000) return J({ error: 'bad_input' }, 400);
    try { const r = await db.prepare('UPDATE users SET balance=balance+?1 WHERE id=?2').bind(C(amt), id).run(); if (!r.meta.changes) return J({ error: 'no_player' }, 409) } catch (e) { return J({ error: 'insufficient_balance' }, 409) }
    await log(amt > 0 ? 'add balance' : 'remove balance', 'player ' + id + ' ' + amt + ' birr');
    await say(env, id, amt > 0 ? `✅ ${amt} ብር ወደ ቀሪ ሂሳብዎ ተጨምሯል።` : `ℹ️ ${-amt} ብር ከቀሪ ሂሳብዎ በአስተዳዳሪ ተቀንሷል።`);
    return J({ ok: true, balance: B((await db.prepare('SELECT balance FROM users WHERE id=?').bind(id).first()).balance) });
  }
  if (name === 'ban' || name === 'unban') {
    const id = Math.floor(Number(b.id)); if (!(id > 0)) return J({ error: 'bad_input' }, 400);
    if (name === 'ban') await db.prepare('INSERT OR IGNORE INTO bans(id) VALUES(?)').bind(id).run(); else await db.prepare('DELETE FROM bans WHERE id=?').bind(id).run();
    cfg.t = 0;
    await log(name, 'player ' + id);
    return J({ ok: true });
  }
  if (name === 'rounds') {
    const r = (await db.prepare('SELECT r.id,r.status,r.stake_c,(SELECT COUNT(DISTINCT user_id) FROM picks WHERE round_id=r.id) players,(SELECT COUNT(*) FROM picks WHERE round_id=r.id) cards FROM rounds r ORDER BY r.id DESC LIMIT 30').all()).results;
    return J({ items: r.map(x => ({ id: x.id, status: x.status, players: x.players, pot: B(x.cards * x.stake_c) })) });
  }
  if (name === 'set-stake') {
    const st = Number(b.stake); if (!(st >= 1 && st <= 1000)) return J({ error: 'bad_input' }, 400);
    await setSet(env, 'stake', String(st)); await log('set stake', st + ' birr (from the next round)'); await poke(env);
    return J({ ok: true, stake: st });
  }
  if (name === 'pause') {
    await setSet(env, 'paused', b.paused ? '1' : '0'); await log(b.paused ? 'pause game' : 'resume game', ''); await poke(env);
    return J({ ok: true, paused: !!b.paused });
  }
  if (name === 'log') {
    const r = (await db.prepare('SELECT ts,actor,action,detail FROM admin_log ORDER BY id DESC LIMIT 30').all()).results;
    return J({ items: r });
  }
  if (name === 'weekly') { // the weekly bonus: ON/OFF state, this period (live) and the finished period (can be paid once)
    const wc = await wkCfg(env), now = Date.now(), run = wkRunning(wc, now), pr = await prizesOf(env), fin = wc.start > 0 && !run;
    const paid = fin ? !!(await db.prepare('SELECT 1 x FROM wk_paid WHERE week=?').bind(wc.start).first()) : false;
    return J({ prizes: pr, running: run, start_ts: wc.start, ends_ts: wc.end, now,
      this_week: run ? wkRows(await wkTop(env, wc.start, 10), pr) : [], last_week: fin ? wkRows(await wkTop(env, wc.start, 10), pr) : [], last_paid: paid });
  }
  if (name === 'wk-start') { // the admin switches the weekly bonus ON now; it runs for the chosen number of days (default 7) or until "Stop now"
    const wc = await wkCfg(env), now = Date.now();
    if (wkRunning(wc, now)) return J({ error: 'already_on' }, 409);
    if (wc.start > 0) { // do not lose the previous period: if it has prizes and players but was never paid, the admin must pay it first (or clear the prizes)
      const pr = await prizesOf(env);
      if (pr.some(x => x > 0) && !(await db.prepare('SELECT 1 x FROM wk_paid WHERE week=?').bind(wc.start).first()) && (await wkTop(env, wc.start, 1)).length) return J({ error: 'pay_first' }, 409);
    }
    const days = Math.min(30, Math.max(1, Math.floor(Number(b.days) || 7)));
    await setSet(env, 'wk_cfg', JSON.stringify({ on: true, start: now, end: now + days * 864e5 })); wkCache = { w: 0, t: 0, top: [] };
    await log('start weekly bonus', days + ' days');
    return J({ ok: true, days });
  }
  if (name === 'wk-stop') { // the admin switches the weekly bonus OFF now; games stop counting and the finished period can be paid
    const wc = await wkCfg(env), now = Date.now();
    if (!wkRunning(wc, now)) return J({ error: 'not_on' }, 409);
    await setSet(env, 'wk_cfg', JSON.stringify({ on: false, start: wc.start, end: now })); wkCache = { w: 0, t: 0, top: [] };
    await log('stop weekly bonus', '');
    return J({ ok: true });
  }
  if (name === 'set-prizes') { // "3000, 2000, 1000, 500, 500 ..." = prize for rank 1, 2, 3 ... (up to 10). Empty = no prizes.
    const parts = String(b.prizes ?? '').split(/[\s,;]+/).filter(Boolean), pr = [];
    for (const x of parts) { const v = Number(x); if (!isFinite(v) || v < 0 || v > 1000000) return J({ error: 'bad_input' }, 400); pr.push(v) }
    if (pr.length > 10) return J({ error: 'bad_input' }, 400);
    await setSet(env, 'wk_prizes', JSON.stringify(pr)); await log('set weekly prizes', pr.join(', ') || 'none');
    return J({ ok: true, prizes: pr });
  }
  if (name === 'pay-weekly') { // pays the FINISHED period's top players (a period can only be paid once) and sends each one a congratulations message
    const wc = await wkCfg(env), now = Date.now();
    if (!(wc.start > 0) || wkRunning(wc, now)) return J({ error: 'wk_running' }, 409); // the weekly bonus must be stopped (or finished) first
    const lw = wc.start, pr = await prizesOf(env);
    if (!pr.some(x => x > 0)) return J({ error: 'no_prizes' }, 400);
    const win = (await wkTop(env, lw, pr.length)).map((x, i) => ({ pos: i + 1, id: x.id, name: x.n, games: x.g, prize_c: C(pr[i] || 0) })).filter(x => x.prize_c > 0);
    if (!win.length) return J({ error: 'no_winners' }, 409);
    try {
      await db.batch([db.prepare('INSERT INTO wk_paid(week,ts) VALUES(?,?)').bind(lw, Date.now()), // fails if this period was already paid, so nothing below is applied
        ...win.map(x => db.prepare('INSERT INTO wk_winners(week,pos,user_id,name,prize_c,games) VALUES(?,?,?,?,?,?)').bind(lw, x.pos, x.id, x.name, x.prize_c, x.games)),
        ...win.map(x => db.prepare('UPDATE users SET balance=balance+? WHERE id=?').bind(x.prize_c, x.id))]);
    } catch (e) { return J({ error: 'already_paid' }, 409) }
    await log('pay weekly prizes', win.length + ' players, ' + B(win.reduce((a, x) => a + x.prize_c, 0)) + ' birr');
    await Promise.all(win.map(x => say(env, x.id, `🏆 እንኳን ደስ አለዎት! የሳምንቱ ከፍተኛ ተጫዋች ራንክ አሸናፊ ሆነዋል!\nደረጃ #${x.pos} · ጨዋታ ${x.games} · ሽልማት ${B(x.prize_c)} ብር ወደ ቀሪ ሂሳብዎ ተጨምሯል።`, playKb(env))));
    return J({ ok: true, paid: win.length, total: B(win.reduce((a, x) => a + x.prize_c, 0)) });
  }
  if (name === 'bonus') { // what the admin has set (the only place the secret cartela numbers are ever shown)
    if (!env.HUB) return noHub();
    const cr = await hubOf(env).current(), raw = await db.prepare("SELECT v FROM settings WHERE k='bonus'").first(); let cf = null; try { cf = raw && JSON.parse(raw.v) } catch (e) { }
    const on = !!(cf && cf.on && Array.isArray(cf.items) && cf.items.length);
    const wins = on ? (await db.prepare('SELECT cartela,name FROM bonus_wins WHERE round_id=?').bind(cf.round).all()).results : [];
    return J({ on, round: on ? cf.round : null, current: cr.id, status: cr.status,
      items: on ? cf.items.map(i => ({ c: i.c, amount: B(i.a), won: (wins.find(w => w.cartela === i.c) || {}).name || null })) : [] });
  }
  if (name === 'set-bonus') { // cartelas like "7, 12, 33" (all use the amount field) or "7=50, 12=100" (own amount each)
    if (!env.HUB) return noHub();
    const items = [], seen = new Set(), def = Number(b.amount);
    for (const part of String(b.cartelas || '').split(/[\s,;]+/).filter(Boolean)) {
      const m = part.match(/^(\d{1,3})(?:[=:](\d+(?:\.\d+)?))?$/); if (!m) return J({ error: 'bad_input' }, 400);
      const c = Number(m[1]), a = m[2] !== undefined ? Number(m[2]) : def;
      if (!(c >= 1 && c <= TOTAL) || !(a >= 1 && a <= 100000)) return J({ error: 'bad_input' }, 400);
      if (!seen.has(c)) { seen.add(c); items.push({ c, a: C(a) }) }
    }
    if (!items.length || items.length > 20) return J({ error: 'bad_input' }, 400);
    const cr = await hubOf(env).current(), first = cr.status === 'lobby' ? cr.id : cr.id + 1; // empty round = the open round, or the next one if a game is running
    const round = String(b.round ?? '').trim() === '' ? first : Math.floor(Number(b.round));
    if (!(round >= first && round <= first + 100)) return J({ error: 'bad_round' }, 400);
    if (round === cr.id && cr.status === 'lobby') { // a cartela already taken in the open round cannot be a bonus any more
      const taken = (await db.prepare('SELECT cartela FROM picks WHERE round_id=?').bind(round).all()).results.map(x => x.cartela);
      if (items.some(i => taken.includes(i.c))) return J({ error: 'bonus_taken' }, 409);
    }
    await setSet(env, 'bonus', JSON.stringify({ on: true, round, items }));
    await log('set bonus', 'round ' + round + ' · ' + items.map(i => i.c + '=' + B(i.a)).join(' '));
    await poke(env);
    return J({ ok: true, round });
  }
  if (name === 'clear-bonus') {
    await setSet(env, 'bonus', JSON.stringify({ on: false })); await log('clear bonus', ''); await poke(env);
    return J({ ok: true });
  }
  if (name === 'accounts') return J({ items: await accountsFor(env, url, true) }); // deposit accounts shown to players (Admin > Accounts)
  if (name === 'set-account') {
    const bank = String(b.bank || ''), number = String(b.number ?? '').replace(/[\u0000-\u001f]/g, '').trim(), nm = String(b.name ?? '').replace(/[\u0000-\u001f]/g, '').trim();
    if (!Object.keys(BANKS).includes(bank) || number.length < 4 || number.length > 30 || nm.length < 2 || nm.length > 40) return J({ error: 'bad_input' }, 400);
    const raw = await db.prepare("SELECT v FROM settings WHERE k='accounts'").first(); let cur = {}; try { cur = (raw && JSON.parse(raw.v)) || {} } catch (e) { }
    cur[bank] = { a: number, h: nm }; await setSet(env, 'accounts', JSON.stringify(cur)); await log('set account', bank + ' ' + number + ' ' + nm);
    return J({ ok: true });
  }
  if (name === 'set-account-image') {
    const bank = String(b.bank || ''), data = String(b.data || '');
    if (!Object.keys(BANKS).includes(bank) || !/^data:image\/jpeg;base64,[A-Za-z0-9+\/=]+$/.test(data) || data.length > 400000) return J({ error: 'bad_image' }, 400);
    await db.prepare('INSERT INTO account_imgs(bank,data,ts) VALUES(?1,?2,?3) ON CONFLICT(bank) DO UPDATE SET data=?2,ts=?3').bind(bank, data, Date.now()).run(); await log('set account picture', bank);
    return J({ ok: true });
  }
  if (name === 'clear-account-image') {
    const bank = String(b.bank || ''); if (!Object.keys(BANKS).includes(bank)) return J({ error: 'bad_input' }, 400);
    await db.prepare('DELETE FROM account_imgs WHERE bank=?').bind(bank).run(); await log('remove account picture', bank);
    return J({ ok: true });
  }
  if (name === 'autotake') { // admin: state of the automatic cartela taking
    let cf = {}; try { const raw = await db.prepare("SELECT v FROM settings WHERE k='autotake'").first(); cf = (raw && JSON.parse(raw.v)) || {} } catch (e) { }
    const sup = cf.uid ? await db.prepare('SELECT id,name,balance FROM users WHERE id=?').bind(cf.uid).first() : null;
    const cr = env.HUB ? await hubOf(env).current() : null;
    const taken = cr && cf.uid ? (await db.prepare('SELECT COUNT(*) c FROM picks WHERE round_id=? AND user_id=?').bind(cr.id, cf.uid).first()).c : 0;
    return J({ on: !!cf.on, count: cf.n || 0, support: cf.uid || '', support_name: sup ? sup.name : null, balance: sup ? B(sup.balance) : null, round: cr ? cr.id : null, status: cr ? cr.status : null, taken });
  }
  if (name === 'set-autotake') { // {on:true, support:<telegram id>, count:<1-30>}  or  {on:false}
    let cf = {}; try { const raw = await db.prepare("SELECT v FROM settings WHERE k='autotake'").first(); cf = (raw && JSON.parse(raw.v)) || {} } catch (e) { }
    const on = !!b.on; let n = cf.n || 0, uid = cf.uid || 0;
    if (b.count !== undefined && String(b.count).trim() !== '') { n = Math.floor(Number(b.count)); if (!(n >= 1 && n <= 30)) return J({ error: 'bad_input' }, 400) }
    if (b.support !== undefined && String(b.support).trim() !== '') uid = Math.floor(Number(String(b.support).replace(/\D/g, '')));
    if (on) {
      if (!(n >= 1) || !(uid > 0)) return J({ error: 'no_support' }, 400);
      if (!(await db.prepare('SELECT id FROM users WHERE id=?').bind(uid).first())) return J({ error: 'no_player' }, 409);
    }
    await setSet(env, 'autotake', JSON.stringify({ on, n, uid })); await log(on ? 'autotake ON' : 'autotake OFF', 'support ' + uid + ' · ' + n + ' cartelas per round'); await poke(env);
    return J({ ok: true, on });
  }
  if (name === 'game' || name === 'game-start' || name === 'game-stop') {
    if (!env.HUB) return noHub();
    const hub = hubOf(env); let r = await hub.current();
    if (name === 'game-stop' && (r.status === 'lobby' || r.status === 'running')) {
      await refundAndClose(env, r, r.status, Date.now()); // cancels the round and returns every stake
      await log('cancel round', 'round ' + r.id); await hub.invalidate(); r = await hub.current();
    }
    const c = await db.prepare('SELECT COUNT(DISTINCT user_id) p,COUNT(*) c FROM picks WHERE round_id=?').bind(r.id).first();
    return J({ ok: true, status: r.status, round: r.id, stake: B(r.stake_c), next_stake: Number((await getSet(env, 'stake')) || env.STAKE || 10), paused: (await getSet(env, 'paused')) === '1', players: c.p, cards: c.c });
  }
  return J({ error: 'not_found' }, 404);
}

/* ---------- HTTP routes ---------- */
const errOf = e => /CHECK/.test(e.message) ? 'insufficient_balance' : /UNIQUE|PRIMARY/.test(e.message) ? 'taken' : 'server_error';
// runs a database action; if it fails for a temporary reason (not "not enough balance" and not "already taken") it waits a moment and tries once more
const retryDb = async fn => { try { return await fn() } catch (e) { if (errOf(e) !== 'server_error') throw e; await new Promise(r => setTimeout(r, 200)); return await fn() } };
async function route(req, env, url) {
  const p = url.pathname, db = env.DB, now = Date.now();
  if (p === '/') return J({ ok: true });
  if (p === '/sms' && req.method === 'POST') { // the phone(s) that receive the money forward every incoming bank SMS here (Telebirr, Dashen, BOA, CBE)
    if (req.headers.get('x-secret') !== env.SMS_SECRET) return J({ error: 'forbidden' }, 403);
    await ensureTables(env);
    const raw = await req.text(); let text = raw, from = ''; try { const o = JSON.parse(raw); text = o.text || o.message || o.body || o.content || raw; from = String(o.from || o.sender || o.address || o.number || '') } catch (e) { }
    const s = parseSms(text); if (!s) return J({ ok: true, parsed: false });
    if (from) { // FAKE-SMS GUARD: a bank SMS must come from a bank sender (a short code or a name), never from a normal mobile number. If SMS_SENDERS is set, only those exact senders are accepted.
      const f = from.trim(), allow = String(env.SMS_SENDERS || '').split(',').map(x => x.trim().toLowerCase()).filter(Boolean);
      if (allow.length ? !allow.includes(f.toLowerCase()) : !!normPhone(f)) { await notifyAdmins(env, '🚨 አጠራጣሪ SMS ተቀባይነት አላገኘም (ከባንክ አይደለም) — ላኪ: ' + f + '\n' + String(text).slice(0, 200)); return J({ ok: true, ignored: 'sender' }) }
    }
    await db.prepare('INSERT OR IGNORE INTO sms_log(txid,amount_c,raw,ts) VALUES(?,?,?,?)').bind(s.txid, s.amount_c, String(text).slice(0, 500), now).run();
    await tryMatch(env, s.txid); return J({ ok: true, parsed: true, bank: s.bank });
  }
  if (p === '/tg/' + env.TG_SECRET && req.method === 'POST') { await onTelegram(env, await req.json()); return J({ ok: true }) }
  if (p.startsWith('/acc/') && req.method === 'GET') { // account pictures (public: they only show the account players pay into)
    const k = p.slice(5).replace(/\.jpg$/, ''); if (!Object.keys(BANKS).includes(k)) return J({ error: 'not_found' }, 404);
    await ensureTables(env); let r = await db.prepare('SELECT data FROM account_imgs WHERE bank=?').bind(k).first(); if (!r && IMG_DEF[k]) r = { data: IMG_DEF[k] }; if (!r) return J({ error: 'not_found' }, 404);
    return new Response(Uint8Array.from(atob(r.data.split(',')[1]), c => c.charCodeAt(0)), { headers: { 'content-type': 'image/jpeg', 'cache-control': 'public, max-age=300' } });
  }
  if (!p.startsWith('/api/')) return J({ error: 'not_found' }, 404);
  if (p.startsWith('/api/admin/')) return adminRoute(req, env, url);
  const tu = await verifyInit(req.headers.get('x-init-data'), env.BOT_TOKEN); if (!tu) return J({ error: 'unauthorized' }, 401);
  // Look the player up with a plain read first. A write happens only for a brand-new player or when the bonus period changes.
  const selUser = () => db.prepare('SELECT * FROM users WHERE id=?').bind(tu.id);
  let u = await selUser().first();
  if (!u) u = (await db.batch([db.prepare('INSERT INTO users(id,name,created_ts) VALUES(?,?,?) ON CONFLICT(id) DO NOTHING').bind(tu.id, tu.first_name || 'player', now), refreshBonusStmt(env, tu.id, now), selUser()]))[2].results[0];
  else if (u.bonus_period < bonusPeriod(now) || (bonusC(env) === 0 && u.bonus_c !== 0)) { await refreshBonusStmt(env, u.id, now).run(); u = await selUser().first() }
  const b = req.method === 'POST' ? await req.json().catch(() => ({})) : {};
  const need = () => u.phone ? null : J({ error: 'not_registered' }, 403);
  if (p !== '/api/me' && await isBanned(env, u.id)) return J({ error: 'banned' }, 403);
  if (p === '/api/me') { const dep = (await db.prepare('SELECT amount_c,status,ts FROM deposits WHERE user_id=? ORDER BY id DESC LIMIT 10').bind(u.id).all()).results, wd = (await db.prepare('SELECT amount_c,status,ts FROM withdrawals WHERE user_id=? ORDER BY id DESC LIMIT 10').bind(u.id).all()).results; const accounts = url.searchParams.get('acc') ? await accountsFor(env, url, false) : undefined; return J({ accounts, id: u.id, name: u.name, phone: u.phone, registered: !!u.phone, balance: B(u.balance), bonus: B(u.bonus_c), deposits: dep.map(x => ({ ...x, amount: B(x.amount_c) })), withdrawals: wd.map(x => ({ ...x, amount: B(x.amount_c) })) }) }
  if (p === '/api/register') { if (u.phone) return J({ error: 'already_registered' }, 409); const ph = normPhone(b.phone), nm = String(b.name || '').trim().slice(0, 30); if (!ph || nm.length < 2) return J({ error: 'bad_input' }, 400);
    try { const rr = await db.prepare("UPDATE users SET name=?1,phone=?2 WHERE id=?3 AND (phone IS NULL OR phone='')").bind(nm, ph, u.id).run(); if (!rr.meta.changes) return J({ error: 'already_registered' }, 409) } catch (e) { return J({ error: 'phone_used' }, 409) }
    await say(env, u.id, 'እንኳን ደስ አሎት ተመዝግበዋል', playKb(env)); // registered: no bonus, just the congratulations with the play button
    return J({ ok: true }) }
  if (p === '/api/state') { // the hot path: answered from the GameHub's memory, no database work beyond the player lookup above
    if (!env.HUB) return noHub();
    return J(await hubOf(env).state({ id: u.id, auto_off: u.auto_off, balance: u.balance, bonus_c: u.bonus_c }));
  }
  if (p === '/api/leaderboard') return J(await leaderboard(env, u, url.searchParams.get('period')));
  const bad = need(); if (bad) return bad;
  if (p === '/api/auto') { // Automatic on/off for this player
    await db.prepare('UPDATE users SET auto_off=?1 WHERE id=?2').bind(b.auto ? 0 : 1, u.id).run();
    if (env.HUB) await hubOf(env).manualChanged().catch(() => { });
    return J({ ok: true, auto: !!b.auto });
  }
  if (p === '/api/bingo') { // manual BINGO button
    if (!env.HUB) return noHub();
    const r = await hubOf(env).bingo({ id: u.id });
    if (r.error) return J({ error: r.error }, 409);
    return J(r.state);
  }
  if (p === '/api/pick' || p === '/api/unpick') { // 2 database round trips: the player lookup above + one batch that also returns the fresh balance
    if (!env.HUB) return noHub();
    const no = Math.floor(Number(b.cartela)); if (!(no >= 1 && no <= TOTAL)) return J({ error: 'bad_input' }, 400);
    const hub = hubOf(env), r = await hub.current();
    if (r.status !== 'lobby' || now - r.start_ts >= LOBBY_MS) return J({ error: 'round_closed' }, 409);
    if (p === '/api/pick' && (await getSet(env, 'paused')) === '1') return J({ error: 'paused' }, 409);
    const bcf = await hub.bonusCfg(r.id); // is this a secret-bonus round? (kept in the GameHub memory, no database read)
    if (p === '/api/unpick' && bcf) return J({ error: 'locked' }, 409); // bonus round: a taken cartela can never be dropped or changed
    const selMe = db.prepare('SELECT id,auto_off,balance,bonus_c FROM users WHERE id=?').bind(u.id);
    let me;
    try {
      if (p === '/api/pick') {
        const res = await retryDb(() => db.batch([
          db.prepare("INSERT INTO picks(round_id,cartela,user_id,bonus_c) SELECT ?1,?2,?3,MIN(?5,(SELECT bonus_c FROM users WHERE id=?3)) WHERE (SELECT COUNT(*) FROM picks WHERE round_id=?1 AND user_id=?3)<?4 AND EXISTS(SELECT 1 FROM rounds WHERE id=?1 AND status='lobby')").bind(r.id, no, u.id, MAXC, r.stake_c),
          db.prepare("UPDATE users SET bonus_c=bonus_c-(SELECT bonus_c FROM picks WHERE round_id=?1 AND cartela=?2 AND user_id=?3),balance=balance-(?4-(SELECT bonus_c FROM picks WHERE round_id=?1 AND cartela=?2 AND user_id=?3)) WHERE id=?3 AND EXISTS(SELECT 1 FROM picks WHERE round_id=?1 AND cartela=?2 AND user_id=?3)").bind(r.id, no, u.id, r.stake_c),
          selMe]));
        if (res[0].meta.changes === 0) return J({ error: 'max_cards', max: MAXC }, 409);
        me = res[2].results[0];
      } else {
        const res = await retryDb(() => db.batch([
          db.prepare("UPDATE users SET bonus_c=MIN(?5,bonus_c+(SELECT bonus_c FROM picks WHERE round_id=?1 AND cartela=?2 AND user_id=?3)),balance=balance+(?4-(SELECT bonus_c FROM picks WHERE round_id=?1 AND cartela=?2 AND user_id=?3)) WHERE id=?3 AND EXISTS(SELECT 1 FROM picks WHERE round_id=?1 AND cartela=?2 AND user_id=?3) AND EXISTS(SELECT 1 FROM rounds WHERE id=?1 AND status='lobby')").bind(r.id, no, u.id, r.stake_c, bonusC(env)),
          db.prepare("DELETE FROM picks WHERE round_id=?1 AND cartela=?2 AND user_id=?3 AND EXISTS(SELECT 1 FROM rounds WHERE id=?1 AND status='lobby')").bind(r.id, no, u.id),
          selMe]));
        me = res[2].results[0];
      }
    } catch (e) { return J({ error: errOf(e) }, 409) }
    // The pick above succeeded, so the stake was paid. Only now can a bonus cartela win — a player without enough balance never gets here, so no bonus is shown for them.
    let won = null;
    if (p === '/api/pick' && bcf) { const it = bcf.items.find(x => x.c === no); if (it) { won = await awardBonus(env, r.id, no, u, it.a); if (won) me = await selMe.first() } } // the bonus changed the balance: read it again
    const st = await hub.picked(p === '/api/pick' ? 'pick' : 'unpick', r.id, no, u.id, u.name, me, won);
    if (won) {
      await say(env, u.id, `🎉 እንኳን ደስ አለዎት! ካርቴላ #${no} በመያዝ የ${won.amount} ብር ቦነስ አሸንፈዋል! ገንዘቡ ወደ ቀሪ ሂሳብዎ ተጨምሯል።`, playKb(env));
      return J({ ...st, bonus_won: won.amount });
    }
    return J(st);
  }
  if (p === '/api/deposit') {
    const amt = Number(b.amount), txid = String(b.txid || '').toUpperCase().replace(/[^A-Z0-9]/g, ''), method = Object.keys(BANKS).includes(b.method) ? b.method : 'telebirr';
    if (!(amt >= MIN_DEP) || txid.length < 8 || txid.length > 24) return J({ error: 'bad_input', min: MIN_DEP }, 400);
    const r = await makeDeposit(env, u, amt, txid, method); if (r.error) return J({ error: r.error }, 409);
    return J({ status: r.status, balance: B((await db.prepare('SELECT balance FROM users WHERE id=?').bind(u.id).first()).balance) });
  }
  if (p === '/api/withdraw') {
    const amt = Number(b.amount), account = String(b.account || '').trim().slice(0, 40), method = Object.keys(WD_BANKS).includes(b.method) ? b.method : 'telebirr';
    if (!(amt >= MIN_WD) || !account) return J({ error: 'bad_input', min: MIN_WD }, 400);
    const r = await makeWithdrawal(env, u, amt, account, method); if (r.error) return J({ error: r.error }, r.error === 'deposit_required' ? 403 : 409);
    return J({ status: 'pending' });
  }
  return J({ error: 'not_found' }, 404);
}
export default {
  async fetch(req, env) {
    const cors = { 'access-control-allow-origin': env.ALLOW_ORIGIN || '*', 'access-control-allow-headers': 'content-type,x-init-data,x-admin-key', 'access-control-allow-methods': 'GET,POST,OPTIONS' };
    if (req.method === 'OPTIONS') return new Response(null, { headers: cors });
    let res; try { res = await route(req, env, new URL(req.url)) } catch (e) { res = J({ error: 'server_error', detail: String(e.message || e) }, 500) }
    for (const [k, v] of Object.entries(cors)) res.headers.set(k, v); return res;
  }
};

// Default account pictures (the logos you sent). A picture the admin adds in Admin > Accounts replaces these.
const IMG_DEF = {
  cbe: 'data:image/jpeg;base64,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',
  telebirr: 'data:image/jpeg;base64,/9j/4AAQSkZJRgABAQAAAQABAAD/2wBDAAUDBAQEAwUEBAQFBQUGBwwIBwcHBw8LCwkMEQ8SEhEPERETFhwXExQaFRERGCEYGh0dHx8fExciJCIeJBweHx7/2wBDAQUFBQcGBw4ICA4eFBEUHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh4eHh7/wAARCADgAOEDASIAAhEBAxEB/8QAHwAAAQUBAQEBAQEAAAAAAAAAAAECAwQFBgcICQoL/8QAtRAAAgEDAwIEAwUFBAQAAAF9AQIDAAQRBRIhMUEGE1FhByJxFDKBkaEII0KxwRVS0fAkM2JyggkKFhcYGRolJicoKSo0NTY3ODk6Q0RFRkdISUpTVFVWV1hZWmNkZWZnaGlqc3R1dnd4eXqDhIWGh4iJipKTlJWWl5iZmqKjpKWmp6ipqrKztLW2t7i5usLDxMXGx8jJytLT1NXW19jZ2uHi4+Tl5ufo6erx8vP09fb3+Pn6/8QAHwEAAwEBAQEBAQEBAQAAAAAAAAECAwQFBgcICQoL/8QAtREAAgECBAQDBAcFBAQAAQJ3AAECAxEEBSExBhJBUQdhcRMiMoEIFEKRobHBCSMzUvAVYnLRChYkNOEl8RcYGRomJygpKjU2Nzg5OkNERUZHSElKU1RVVldYWVpjZGVmZ2hpanN0dXZ3eHl6goOEhYaHiImKkpOUlZaXmJmaoqOkpaanqKmqsrO0tba3uLm6wsPExcbHyMnK0tPU1dbX2Nna4uPk5ebn6Onq8vP09fb3+Pn6/9oADAMBAAIRAxEAPwD4yooooAKKKKACiiigAoora8M+Hdc8T6mul+HtKvNSu36RW0Zc/U+g9zSlJRV27IaTbsjFor6z+F37H+qXgW88faymmJgN9hscSTfR5D8i/hu+tfSngL4PfDjwTGh0LwtYfaV/5fLhPPn/AO+myR+FY+1lL+HG/m9F/n+BXKl8TPz28JfCP4k+LCr6L4O1SaNv+W0kXkx/XdJgH8K9V8P/ALH3xHvismrajoOkRns0zTP+SjH/AI9X3lRT5KrWsreiX63DmitkfIOlfsVR5zq3j5n/ANi103b+rSf0rcj/AGMPBv8Ay08Za9/wGGIf0r6ioodBPWTb+bX5WD2j6JfcfLkn7F/hD+Dxhrq/70MR/pWDqn7FRyTpfxAU/wCxc6d/VZP6V9g0UvYJfDJr53/O4c76pfcfA3iL9kP4m6eJJNMutE1aNenl3DRyN+DDH615P4t+GHxA8Jjd4g8JapZRg/64xb4/++0yv61+qNDfPT5asdpX9V/lb8gvHqj8eqK/Tvx/8Dfhj40Vn1PwvaWt4/8Ay92CfZpt3qSvDf8AAs180fFD9kTxPpCSXvgjUo9ft1P/AB5zgRXP4H7jfpS9s4/xI2/Ff5/erByp/Cz5borS13SdU0PUpdM1ewuLC8hb54Z0KMv4Gs2tk01dbENWCiiimAUUUUAFFFFABRRRQAUUUUAFFFFABTlFXtE0vUNa1e30vSrWW8vbqQRwwwrlnY9gK+7f2c/2bdI8ExW3iPxfHDqXiTaHSFsNBYt7D+N/f8qzqVOV8sVd9v8AMqMb6vY8W+BH7L3iDxZ9n1vxn52h6M+Hjt+l1cr9D/qx7nn2r7O8BeCfDHgbSE0zwvotvp9v0fam6SVvVnPLH610dFSqN3zTd3+HyX9PzG56WWiCiiitiAooooAKKKKACiiigAooooAKKKKAOQ+JHw58IfELTvsHifRobk/8sblfkuIfdZByPp92viX47fs3eJ/h/wCdq+hCbX/Dy/MZ44/9Itl/6aIOo/214+lfoTQy1i6XK+am7P8AB/133L5+j1Px6or7h/aT/Zls9ciufFfw6tEs9V5luNLXCw3HqY/7j+3Q+1fFF7bXFjdy2d3DLBPC5SSKRSrIw4IIPQ1VOpzaNWa6f1/XezE421WxVooorQkKKKKACiiigAooooAK0dD0rUdc1e20jSrWa8v7qQRwQxjLOx7VTijeSVUjXczdFWvv79kP4LJ4E8Pp4o8RWif8JNqEfyIwz9iiPRP989T+Xas6s3H3Y/E/6uVGN9Wbf7NnwQ0z4W6QNQvxDe+KbuP/AEq56rAv/PKL0H95u+PpXs9FFOEFBf1r/X4bIJS5goooqyQooooAKKKKACiiigAooooAKKKKACiiigAooooAK8B/al+Aln8QtNl8R+G4IrbxRbj58fKt6o/hb/b9D+Fe/UVnUpqa7NbPsVGVj8hb21uLK7ms7uB4biCQxzRNwyMDggjsc1Ur7g/bN+CKa3p1z8RPC9of7VtF36nbxJ/x8xD/AJaAd3QdfUD2r4fop1Oa6ejW/wDXn/wOgSVtVsFFFFaEhRRRQAUUV0PgDwzf+MPGOl+GNNU/adRuBEp/ujqzH2Cgn8KTaim3shpXdj3/APYh+EieI9f/AOE+12136Vpc22wjkT5Z7kc7vcJx+P0r7lrF8D+G9M8H+EdN8OaTHss7CERJ/tern3JyfxrarKjF6zlu/wAOy+X53Km1stkFFFFbEBRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFAAy1+e37YXwlHw/8bHXNGg2+HtZkZ4dv3bafkvF7DuPxH8NfoTXI/F/wTYfEL4f6p4YvtmbiPdazf88Jxyj/AJ4/DNY1U4/vI7r8V/W3mXDXRn5UUVo69pV7out3mkalC0N5ZTNBOh6qynBrOrVNNXWxDVgooopgFfY3/BPvwAPL1X4h39v62Gn7/wADK4/Rfzr5AtYZbq4SCBGeWVgiIvUseAK/VT4SeFIvBXw20LwxF5e+ys1WZ0XG6UjMj/i5JrGp70ow+b+X/B/IuOibOqooorYgKKKr6hcx2Vjc3kn+rt4Xlf8A3VBJ/lQBFZ6vpd7fXOn2mp2dze2mPtVtHMryQZ6b0Byv41dr5W/Yzl+2/EbxDqE//H5cad9of/eknDSfrivqmu3H4T6pXdK97W/Iww1b28OewUUUVxG4UUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFAHw9+334DGk+MrHxtYwbLfWF+z3m3p9pjHB/wCBJ/6BXy3X6e/tKeDx42+DWvaYke+8ihN7Z/8AXWL5gB9RkfjX5hVhR91uHbb0f/BuvSxcndKQUUUVuQesfsp+GT4m+O3hyzkRXt7WY3swb+7ENw/8f21+ltfE/wDwTr0hJ/F3ifxBKhzZ2MVqjf8AXVyx/wDRQr7YrGGtSb9F+F/1ZctIpBRRRWxAVw/x61P+yPg74nvI5Nkj2Rt0/wB6UiIf+h13FeJ/tj6n9l+GFhp4/wCYhrESP/1zjSSX+aLXZl9P2uKpx81/mY4mfJRlLyZ4F8FfFsfgX4jabrF2dmnMpstQ/wBmGTHz/wDAHCv9Aa+54ZY54kuLeRHjdQ6OvKsp6EGvzo3x/wDPRK774ZfGHxR4Ctk0+3lt9V0ZPuWF25Hlf9cpByo9uR7V9VnGUzxbVWl8S/E+eyzMY0I+zqbdz7bor58t/wBqTRPL/wBI8Jaqkv8A0zuYnX8yRXovwg+KGl/EqPUv7N0y/wBPk09o96XO0q3mbsYKkj+A8fSvl62W4qhBzqQsl10Pfp4ujVfLCV2d9RRUN1PHa201xPJsjijMrv8A3VAyT+VcNrnQ3YL+7s7K1e4v7uG2t0+/NO4RV/E1IrRvF5kex43/ALtfLnxs+Jtn46sbOw0qwvILK0uHmd7naPP4wpwCcdW6+orvvhR8WtDuf+Ef8Fx6TqNtJ5MdlBMzo67kTHODkA4r1amUV4UFVs763XZHkUs6w1TEOipK2ln3b6fI9fvr6zsokkv7u2tY3YIjzzKisx6AZ71Yr5x/arvo7rxno+kTybLe2tN79dq+bJgn8o69R0D4seANSvYdIsdadJGAih+020kKy9gAzADP1xWVTL6kaEKsU3e7em3/AA5tTzGnLEVKMmlytJa7u36He0UVxHxk8af8IX4Re8tNj6rcSC3skbnaxBJcj0ABP5Vx0qUq01TgtWdtarGjB1J7I6zUtV0vS9n9p6nZ2W/7nnzLHu+mTU9vPb3USXFvPDNG/wBx43BVvoRXzj4K+EOr+N9JTxX4k8QTQT36+bBuTz5pYz0diTwD1AHb0pvwVudY8H/GGbwPPOXt7iWa3nhT/V+YkZlWZB2JVP8Ax7npXqTy2lyz9nV5pQV2rdt/uPKhmlbnh7Wlywm7J3u9dro+kmaNIvMk2Js/jb5ay4/E/ht5Ut4/EWjvI7bNi3kZbd6YzXhnxR1PXPiH8Uv+EA0m7+zadbzGJ+vlsyJulkkA+/jkKnqB68aFz+zpaPGkdv4pl+8N/m2CldvfGH61EcBQpwi8RV5XJXsk3p5lvMK9Sclh6XMouzbdtetvQ95oqvY20dlY21mkjvHbxpFvl5ZsDGSfWrFeUesgooooAK/K740eHP8AhEfip4j8PohSO1vpPIxx+6Y7o/8Ax0iv1Rr4G/b70X+z/jLb6nHHsi1LTYnJ/vOhKH9AtYy92pF97r9f0LjrFo+c6KKK2IPuj/gnhYGH4b69qBTJutVCf8BSMf8AxZr3r4heM9D8CaGmsa9O6W7zC3gSJN8kshBOEH0BP4V5H+wVFs+BG/8A566rO3/oA/pXtHivw14f8VaYlh4h0y21OzSQSxpP/DIAQGBHIOCR+NRgnTveptd3tvuyq3Nry72X5HmP/DR/w/8A+ffXv/AMf/F0f8NH/D//AJ99e/8AAMf/ABdP8V/s7eBNTtX/ALFN5oF7t+R4Zmkh3f7cchOR/ulT7180ePPCOueCPEL6Hr0CeZt82C5jz5NzH03of5jqPyz9VgsHlmMfLByT7P8A4Y8PFYnG4ZczSa76n1J4b+PPgTXfEFholoNYhub2YW8Dz2eF8w9ASCcVofGHx38P/DZs9H8aWn9pyXC/aEs/sYuNqjjec8DuB36182fs76b/AGp8a/D0f/LO0aW9f/tnGcf+PlatftPal/aHxr1WP/lnp9tb2n5J5h/WQ1byigsaqMG7KN3rrvZErMan1R1pJXvZHof/AAs/4B/9CP8A+UGL/Gl/4Wd8A/8AoR0/8EMP+NeLfD3wT4k8fau+n+HbNPLiYfaryfKw22fU9z/sDn+dfRHhH9nHwZp8aSeIru/8QXnG/c5gt/wjQ5/N2qsZSwGEfLOpJvsmGFrYzELmUYpeZz//AAs74B/9COn/AIIYv8a2/D/x3+E+kRJp+kaZf6TbvJ8/kaascaseMkIa7Jfgz8L/APoStN/77kP/ALPVix+E3w3sr6G8tPB2mpc28gdHZGfaw6HBOK82eIy+as1N/NHdGnik94/cztqayxvF5cnzxv8A3qdRXincfL/xb0bQ0+NWl+H9J02zsrNFtIp4baEBfnkMkhIHX5CPyruPhd45+HGs+Lo7fTPB1voeoyq6WVz5Mf71cZxlPuMRnj9a4nxvqcnhL9ou58QatYTXMcNwlwiLgNLEYBGrrnrtwfxU0/wBbSePfjcniPSdITTdLsruO6n242x7B8gOOPMcjOB719ZVpKeFXtL8qhfmv17PvfQ+QpV3DFyVO3M6lnG3RW1T6Jah4007/hOv2irnQ/PdIPOFu80fLLHFDlsZ77gR9TR+0B4F8MeD7LSJ9CS6he6aRJoZJmk3qgB3/NyDz9Oavfs7f8T74u694j+/F5Nxcb/9q4nBX/xzzKt/tcW149/oNx5f+h+TPFv/AIfOJU4J9wP0NOnVnDHUsMpWUY2a7uxFSjTqYCtiXG8pSevVK9l9xrWvxo0/S4rPw5q0F4lxFYQRXWpcFYp2hU7zH1IG4En6/LXkXxP8Jax4Y1O2/tfVodW1DUIXuN8TtIzc4U7267+fyra8f+If+FoeIdE0zw14aNrqKQmJ3baZJM7R85T/AJZJjOT69q2fGdn/AGh+0F4e8ORyedHpi6fZf7yxDznP5E1eGgsLNSS5W03JaPbZ+S8hYuf12Di3zRUoqL1W+/rZdT6L0exj0vR7PT4/9XaQx2//AHwAP6V89/Bhv7d+Put6/J88UX227R/7qvJ5aD/vhz+Ve+eLNR/sjw1quqf8+llLL+SE14d+y9o0l14f8VXCSbJLiFNPgf8Aut5bkn/x9a8bBe7ha9R9bL73qe3jlz4vD0l0bl9y0IP2bk/tr4n+IPEknz/uZZf+BXE+4foGr6Lr5P8AhV44l+F+r6rYatorzyPsinh3iOaCSPPqOQc/yNer+FPjjo+u+JLHR/7Ev7aW9mESTM6OqsemQOcV0Ztgq9Ss6kI3ikrPySOXKMfh6dBUqk7Tbd097tnrNFFFeAfRBRRRQAV8f/8ABRvTiF8G6mP+nqB/x8th/Jvzr7Ar5c/4KKp/xb/wxJ/c1aRfzhP+FY19FGXZr8Xb9S4bteTPh2iiitiD9Bv2C5d/wHWP+7qlwv8A6Cf617/XzN/wTyvzN8LdbsCP+PXV94/4HGv+FfTNYYe3K7d3+bLqb/JfkFeWftReHLfXfhNf6h5afbdE/wCJhA/91U/1o+hTP5D0r1OuV+L1veXvwr8VWdhaTXN5caPcxQwxplmZ42GAO556V6GDqOniISTtqjCrBTg4vZo8A/Yz037V481vVP8Any0xLf8A7/SZ/wDaBrgZNM1D4j/GvUtP01/3mq6xcv53VYIEc/vPwQDHqcDvXtP7N+k6h4I+E/irxRrWmXOn3Eu+4RLmExyeVDCdpKHkfOZOtYn7Eeix58Q+IHj33EUcOnwO33lyPMk598RflX1FTF+zq4nEw+yoxXr1/HU8WOG5qdGhLzbPoHwf4c0fwl4etvD+i26Q2Vuv/Ambu7nu5PJNY/xH+JHhPwFbJJ4hv9lxKu6GzgTfcS+4TsPckCtL4g+I7fwj4M1XxJdx749Pty6J082Q4WNPxcqPxryz9n/wImr23/C0/G8aav4i1hvtFr56B1toekbIDwCw5H91cAY5r5yjSjOMsRiG7J/OT339N2evObTVOnv+SK837SdnBH9sn8AeI4dO/wCflto/mNn/AI/Xp/w7+IPhfx7ZPd+Hr/fLFjz7adNk0Gem9fT3GR711TfPF5cnzxv/AANzXzT8YNDt/hL8U/DHj/wtAmn6df3Jt9Qs4fkj5x5gCDoHTJx0DRg1vShhsY3TpwcJ9Nbp26O5nJ1aPvSd110tY+lqKGrlPGcviCH7TJaPt05Iv4Nm7ng5385+lfO5hjVgqLrODlbpFXfr6Hp4XDvEVFTUkvV2LdxbeF/GFt/pemWOrx28m3/SrYPtb1G8fqK19NsbPS7FLPTLS2s7dPuQwIEVfoBXD+EYNfQrJpkgSxlufn8zYVbZhD/t9FrU1TxPczXv9n6DbfaZef323d+Q6Y/2mO2vIwPEnPgIVsXGUW9lZ+83r7iu29PQ7sRlFsQ4UGmurvt/ielje0nRtL0jzv7I0yz0/wC0SebP9mhWPzW9Tjqafq1tp91pk1vqcFtc2TKfPSdA8e0c8g8VyU+o+MNMH2i/TfH/ANNEjK/QlOV+tamravHfeB7m8t96edi3dG+8rFwpH61tDiOjUVVuMoThFytNNNpK913+8yeVTg4RunGTSvHValjwfY+F7axeTwzplhp8bttf7NbCHcw9eBV5dI0tNYfWP7Ms/wC1Xj8r7Z5K+dt9N/XFZPhi4g0nwYl5dvtjdnl/2my52gepxis5dY8Uavuk0m1MFv8A3vlP/j78H/gIpxz/ANnQpSrpyq1IpuMU29fnt6sbyrmqTjTsoRbV5WS0/rsdlNFHPE8c8aPG6lHRvmVlPUEVlj/hH/CmmQ2cFvbaZZbjshtodi7upOFH61haf4k1SxvUs9ej/dvj52QBlz0b5eGT6VD8SJ86lZx7N/lRhnTp8pcZ/RDXJi+JqccBUr0NJRaTjJNNNvqvS7+81oZTJ4qNOps03dPdeT9bHVapoeh6vIkmp6TYahIn3HubZJGX8xVaw8LeF9Pvk1Cw8PaVa3qKUSaCzRJFU9cECsNdQ8YajH9otLfyLd/ubUQbv+/nJ+uBVnw74jvJNS/srV49lw7bEfZs+bGdjj+RFdlHiahKpGlJTgp6RcotRfkr9/kYVMmmouacZNatJptHRapqFnpdr9pu5NkW7b9wn5vQAVPDNHPElxHJvjZQyf7p6Vz/AI5udPSKzs7+0mufNl3J5T7NuMITn/geMVY8Qa9b6DJDbx2jzfu92xXAVVHA6/54rWpmlOhVqutOKpwUb73Tff10tbvqTDByqU6fs4tylftay/rrY3KK5DS9U8R3tymozoltpaKZX+UfNGFPTPzn68CopPFmqahIlnpGmulw394h2x646D6k1g+I8HGClJSXNflXK+aVusVvbU1/smu5cqadt3dWXk/NddztK+XP+Cisn/Fv/DEf9/VXb8oT/jX0roY1BNMT+1nV7znftx68dOM4r5S/4KO6ji28G6YOrNd3D/h5aj+Z/KvUc3VpwdmrtOz33vr9xxcnJNq97X2+4+NaKKK6jE+s/wDgnTrAh8S+KdAeT/j6tYbpE/65uVYj/v4v6V9pV+bX7IniX/hHPjvoMkj7Le/Z7Cf/AHZBx/4+Fr9JaxhpUnH0f4W/NMuWsUwooorYgwviFp8mr+AvEOl2/wDrLvTLiJP954yBXhH7Ems27J4h0Munmy+Tfwp/eXHluR9P3f8A31X0pXyF8T9B1z4MfFiHxZ4ej/4lV1cvLZO2fJ+fmW0kx0HXHsAeqV7WWWr0auEvZy1Xqun3HBi70pwrdFo/Rn0D+0F4e1DxP8Ite0fTI3mvdsVxDCv3pPKlWUoPchCB74rj/gR8XvCF14J0fw/rWrW2k6pp8Edk8N3+7WXb8qlXPHO0ZHUGux+G/wAVPCHje2h+w38Nlqu399pty4SZW74B/wBYPcfpV3Wvhp4D1fWP7c1PwvYTaikgle52FNzDkM+0gP8AjmueM40qUsNioNWd1bdO1uu6Zs05yVWk1tY66vAv2nZY/EnjPwP8O7P57y4vxdXW370Uf3Rn/gHnH/gNdb8U/jb4P8F2M0VnfW+tayiny7O2mDLG3/TWQcRj26+1YP7PfgjX31u7+J/jvf8A8JDqqn7LDIhRoIWxklP4SQAAn8KD1JrTB0pYaP1qorW+FPq3p9yJrTVV+yj8/JHtzVgePpdnh/y/+e08afkd/wD7LW/WZ4j07+09Ie3jfy5OHQt/eH9O3418zm1GpXwNalS+KUZJerR6uCqQp4iEp7Jox98mn/DiHyPkka2T51/haQ8n/wAfNYfht9ftbZ5dIsEaKZvvGEHpxj7/AEGK1vDdrql1YXnh/VLOWGzWMqkzJhlbPAB6OB1BHpVG0/4STw3M9tFaPc27tvwsDSR7vVdvK59DXxGJU5zw2KaqQpxhye6vejJaO6s3Z7XS1t8j6GlJJVaS5ZScubXZp6/eie8ufGF1bTW8+mp5cqlX/wBGHf8A4HWXqFvd6Z4VEd3G8ElxembY2N2Eixk4/wBrFdJoU/im81NLi/RbayVTvh8nZu44wDl8/lS/EHTri802GS3jaYxMd6RoS211xkAdecVpi8slXwNXFwlVnJRcUppJ2drtJJOzV7fkRRxipYiFCSgk3d8vfpfpe9jC8ZJIkelaPHu/c2sezb/FI58sfyP/AH1V+G88YQRJHHpqIiLsRFth8q/991Y13RrvWdHs7wxbNRSH54d+N3fGexzyKqQ614ujj8g6a80n3PNks5P1IOw/Ws69GWGx1SpUlVhGajyuCvdJW5Xo7Ndti6c/a4eMYqEnFu/N3vv6P/hinrNt4o1rZHd6Z91WRNqqn3/U7+nSp3iTUPHyW8/zxQ4X/f8ALjzj/vvJ/Cuo8NrrCWD/ANtSLJcPIWT7vyr6HHHrWF4l8PXaX39qaRvMvmea6qw3K/8AfXPXvkV0YzJ6lOjHFwU6jcoSmpW5uWN7KyWr116mVHHxlUlQk4xspKLV7XfW52VcR4mWO68dWEUH+sRod+3thy35hP5ilXWvGNyggi03Y+OZfsjp/wChnYP1rU8L+H5NOlfUL+Tzr2XPvtz157k+telisT/bip0KFOShzKUpSTSSTvZX3bdlpokclGisv5qlSSvZpJO979X5epm+IAL3x7YWn/LOEx/oXc/oBUerxR6n8QYbKTDxLtV09kQyH9SBVvTrO7k8eXl3PBKlvFv2OyEBuFRMHvxv6UeHbG7fxdqWoXcEsMa+YqOyY3ZcYI9fkT9a8+WFq4idpQdqle70fwwWnyfLp36HWq0KUbxkvdp9/tM1fGUvk+Grz/bURf8AfZC/1qr4DtI4NES42fvLpizv/sgkKPpgD86Tx9FeT6RDHaW8s+65G9I0J7HH64rY0m2+xaZbWf8AzyhRPyFe7GhKrncqso6QppJ+cm27fJWZ5jmoZeoJ6ylr6Lv8y3Xwb/wUB1n7b8YLHSI+Y9N0xMj0eRixH5bfzr7yr8t/jz4jPiz4weJtcRt0c186Q85/dx/u0x/wFQfxr2p61Yrtd/hb9Tz4/C2cFRRRWxBb0+7uLK/t721cpPbyLLG/91lOQfzr9Wfht4kg8X+BNF8Twf6u/s45XT+7IR84/A5Ffk3X2r/wT88eJdaPqfw9vJR5tmTe6eG/iiY/vUH0chv+BVhU92cZ9Nn89vx0+ZcdU18z6wooorcgKpa1pWn61pk2l6vYQ3tlcLsmhnTKtV2imm07oTVz538Yfsw6fdXPmeFvEMllFu/489Qh+0qv+7ICGA+uawY/2avGc5+x3/jDTUsv+28y/wDfskD9a+pqK9WGd4yKtzX9Ur/ecjwGHbvy29Lnlnwy+BnhDwXcw6hJv1rVYvnS5u0URxN6xxDhT7nJ969Toorz6+Iq15c9SV2dMKcaa5YqyCiiisSwooooAKKKKACiiigAooooAKKKKACiiigAooooA4L9oPxf/wAIT8I/EGuRybLhbc29r/13k+Vf1Ofwr8t6+sv+CgfjwXviDS/ANlPmLT1+23u3/nq4xGn4Jk/8DFfJtYUvelKffRei/wCDcuWiSCiiityArrPhb4vv/AnjzSvFFgW8yymDOn/PSI8On/AlJFcnRSlFSi4vZjTad0frn4Y1mw8R6BY69pUyy2d/Cs8LD0I/nWlXxd+wt8V002+/4Vrrs5S2upDLpLv91JTy0P8AwPkj/az/AHq+0azpSbvGW6/q/wA/+B0KmktVsFFFFakBRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABXOfEnxbp/gbwRqvifUpB9nsoS6J/FLJ0jjHuxwPxro6+DP21PiyfF/iv/hDtFut+haPKfOkjf5bm56E+4T7v13e1Y1pPSEd3+XV/11sXBdXsjwXxdrmoeJvEuo6/qsnm3uoTtcTP7seg9h0/CseiitYpRSS6Ettu7CiiimIKKKKALNpPLa3MVxbu8UsTB0dDhlI5BB7Gv0R/ZW+M1t8TPC/9n6rIieKNNjVLlOn2mPoJ1/qOx+or85a3PB/iPV/CXiO01/Qrx7XUbSTfG69/VSO4PQis6kG/ejuvx8v6/wA07jJbPY/WmivMv2f/AIwaJ8VfDfnwFLPWbVR/aFiz/Mp/vp6ofWvTaKdRVFdClFxdmFFFFaEhRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUV4t+0v8cdM+GGinTtMkivPFV1H/ott95bZT/y1l9v7o/i/Os6lRQXn0Xf+vw3HGNzn/2wvjVH4K0N/Bvhu6T/AISC/j2zujfNYwHqf+ujdv8AvqvgVjV7WtU1DW9WuNU1W6lu7y6kMs80hyzseprPop03G8pbvf8AyHKV9FsFFFFaEhRRRQAUUUUAFFFFAG54P8Sa14T8QW2veH76Sz1CBso8Z6+oI7g+lffv7O/x/wBA+JlsmmamYNJ8UKvz2zPiO59XiJ6/7nUf7XWvzmqzbXE1rcpcQSPDLGwZHjYqysOhBHQ1nOnd80XZ/n6/1+qdxlpZ7H6+UV8XfAn9q+80xYtD+JPnXtsp2R6vEm6aNf8Apqo++PcfN9a+vvDWv6J4j0mHU9C1K21Kzl+5NbOHX/6x9qmNW75ZKz/rb+vWwOGl1sadFFFbEBRRRQAUUUUAFFFFABRRRQAUUUUAFFYXjXxb4c8GaJLq/iTVrbTbNV4eR/mf/ZRBy59hXxn8ef2o9Z8Tx3GheBftGjaO+UkvGO26nHtj/Vj6c/SsZVteWCu/y9X0/PyLUNLvRHsf7R/7R2keBobnw74Ukh1LxJtKO64aCxP+0f43/wBj/vqvhHXdV1DWtXudX1W6lvL26kMk00rbmdj3NUWYsd7/ADFqZVQp8r5pO7/rbsJyvotgooorQkKKKKACiiigAooooAKKKKACiiigArqfAXjvxX4G1L7f4X1m5sJCfnRWzHJ7Mp4auWopSipK0ldDTad0fafwu/bC0+dI7L4haK9nL/z/AOnoXjb3aPqPwzX0f4O8c+EPGFv9o8NeIdO1P/YgmHmL9U6j8RX5O1asbu5srhbi0uJbedDlJYnKsv0IrH2U4/BL79fx3++5XMnuj9e6K/Nfwd+0R8WvDJSODxRLqFuvSHUUE4/M/P8ArXqegfto6/CiRa74M028/vvaXL2/5Ah6anUW8Puat+NvyDli9mfatFfMWmftmeCJf+Qh4W121/65mKRf5itqH9rr4UP/AKyPXk/3rMf0el9YjbVP7n/kHs35fej6Dor58m/a8+FEf3I/EM3+7ZqP5vWDqX7ZvgyHeNN8J63c/wBzzXjjX+bUe3i9k/uf+Qezfl96PqGiviTxB+2b4quY2TQ/CGj2HPytczPcH8hsrynxn8fPit4pZ477xbd21u3/ACxscW6/mvP60+eo9ofe1+l/yDlj1f8AX4H6B+OPiT4E8ExPJ4l8S6dYSbS32bzQ8zY9I1y5/Kvmz4o/thSN51h8PdFCfwf2jqK/qsQ/qfwr5CnmlmmaWZ3d2OWZmyW+pqCl7KUvjl92n/B/FBzJbI6Dxh4s8ReLtVfU/EusXmqXjn78752j0UdFHsAK5+iitklFWSsiW29wooopiCiiigAooooAKKKKAP/Z',
  ebirr: 'data:image/jpeg;base64,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',
  mpesa: 'data:image/jpeg;base64,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'
};
