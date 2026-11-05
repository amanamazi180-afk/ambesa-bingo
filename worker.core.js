// Anbesa Bingo server — Cloudflare Worker + D1 database + Durable Object (GameHub) that runs the live game. 600 CARTELAS.
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
// SPEED: tables are created only once ever (marker schema_v2) + indexes; admin pages read the database in parallel; the admin list is cached 30 s;
//   a pick needs 2 database round trips (the secret-bonus setting is kept in the GameHub memory); the round-end screen no longer waits for the winners' Telegram messages.
// BROADCAST: /broadcast text sends to ALL registered players from ONE command, in the background (about 25 messages per second = Telegram's safe speed). /more = progress, /stopbroadcast = stop.
//   It runs in a separate GameHub instance named "bc" (Durable Object alarms), so it never slows the game.
import { DurableObject } from 'cloudflare:workers';
const LOBBY_MS = 40000, CALL_MS = 4000, REST_MS = 8000, CUT = 0.8, MAXC = 2, TOTAL = 600, MIN_DEP = 30, MIN_WD = 50, MIN_TR = 10;
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
  ebirr: 'data:image/jpeg;base64,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',
  cbe: 'data:image/jpeg;base64,/9j/4AAQSkZJRgABAQAAAQABAAD/2wBDAAQDAwMDAgQDAwMEBAQFBgoGBgUFBgwICQcKDgwPDg4MDQ0PERYTDxAVEQ0NExoTFRcYGRkZDxIbHRsYHRYYGRj/2wBDAQQEBAYFBgsGBgsYEA0QGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBgYGBj/wAARCAEAAQADASIAAhEBAxEB/8QAHwAAAQUBAQEBAQEAAAAAAAAAAAECAwQFBgcICQoL/8QAtRAAAgEDAwIEAwUFBAQAAAF9AQIDAAQRBRIhMUEGE1FhByJxFDKBkaEII0KxwRVS0fAkM2JyggkKFhcYGRolJicoKSo0NTY3ODk6Q0RFRkdISUpTVFVWV1hZWmNkZWZnaGlqc3R1dnd4eXqDhIWGh4iJipKTlJWWl5iZmqKjpKWmp6ipqrKztLW2t7i5usLDxMXGx8jJytLT1NXW19jZ2uHi4+Tl5ufo6erx8vP09fb3+Pn6/8QAHwEAAwEBAQEBAQEBAQAAAAAAAAECAwQFBgcICQoL/8QAtREAAgECBAQDBAcFBAQAAQJ3AAECAxEEBSExBhJBUQdhcRMiMoEIFEKRobHBCSMzUvAVYnLRChYkNOEl8RcYGRomJygpKjU2Nzg5OkNERUZHSElKU1RVVldYWVpjZGVmZ2hpanN0dXZ3eHl6goOEhYaHiImKkpOUlZaXmJmaoqOkpaanqKmqsrO0tba3uLm6wsPExcbHyMnK0tPU1dbX2Nna4uPk5ebn6Onq8vP09fb3+Pn6/9oADAMBAAIRAxEAPwDyWiiiv0Q/WgooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAoooPHWgAooORjIPPTjrQeDyDQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRR2zkfSgAoHJwOtKBk4yPx7Vp6foN3fr5sirbwdfOnO0AZxkenPGTXNisZQwlP2teajHzInNQV5My++MjPp3+v096kggnum228EkrdNqKSR+Fbhj0XSolkulu2uBDJIJb6Fljt1U4DuM9Ceg+8fTFPudX1S5sLe1g09rq0vlSK0jsGe1llbGWkkbrDHgEbANzcnOBXyuI4vi3y4Ok5X2b91fK++z7aJvY4p5hHaCuUIfDmrzDcYEgXGd1wwVf58VNc+HpdNtRc6vqWm2MBYKJblzGmT2yeKi1LVLqSQXNrc2esW0lyRIb5VlhtHQnEMajqwOT5pJJwcZxVORZbK7TUrS6uJVujvYXshnDMG+eORW4ZRxg4BwR0rHDZnm+N5ZwcIRle2m7XTV6PfdJOxMK9epqkki7LpelW0cUl14gthDMP3M8amSE84wZFyoOeMEg0y40mC1it5E1jTpIrkHyZftASOTHUB/u59iaryBNN1BL3S18uC6XzTC/IcDKvG46MARgZHQgggmiQx6VqpktEX7LcIk0lvt+WeMg/I4PBYEEBuowCDXVTq5peLjWUr3snFK9t46bSXq07PVFKVbe6fyI7mzurR1W4gddwyrD5lYYzwRwargg4weozV9vK0bVZLSNTcacwEi2xJCmN1DAqD9xwG6jGTnOahv4GtdRktxIrIhBRguNysAyk+5BFe3gcfKtyxqrWSumr2a66PVNdU+613t1U6rlZSK9FFFeobBRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFByBkAn6UAH05PoKlgtZ7qZIbeEtK5wM8YHqT0A9zRbQNc3ZhiwZNuTzjavdj6AVumS20tjplhqIiuZ3S1kuo7cyvG3yyOQTxtEeBnnBcHtXh5znUMvioQXNUey126ydtor8djmxGIVFebIozoWixCeW7s72ZAruHZnTD52KpQEFmYdPQE1BqN7PE89zrFjZX0cbQxOLaQr9qvBysYGSAka53Kw5KsSORSW11IY7LVd1tdWCGbU5G8hRtVPlhiT5QyEDGD+hpbNBpkGmzyNMulR2s2q3ZkC+ZK4bcoKj+JVGQQf4yRnkV8BU569R18XJyl6vpdtR/lfuuys9eV67ryJOVV81QRrcaSSl7cPNpNvGbvUzIRLJe3RbiJhkhXXcAB6nI4qKacWWsPb3kk81zrKmS8uHzG1vaMNqBem1wemOBsI5zUttaWUDW+jXflzCYSazd3pQFjht0bYBwMjeCO3IHQVm3F7c6jBp9/cviW8a5xGwysaBkKIPYbz+dejl+FjiK0aU/hekmtLp7PyblFrS3uxjdGtKnzSS7/1/wCeztnt47/SljSLy43i2L0SSLJBH4qR9D702ORZfC8h/553EMiewcFSPx+X/AL5qeaZLbXfEV2D+6tfOLezeWFx/30SKoODbeGLG1Y4kup0LDPSOFeSf+BMP1r6GNV1YqX2pexl/29fX/wAlS+R2Kd1p15fvuWbxgNC0t/4vtVxF9QURjj6EUl+R9q0lT3sW3f8Af04/rTZ0kn1mw0iIFpbFCZFH/PeYq236hFXPpk01QmreJJhbSp9njUWkcxOFWNMl5M+md3PtW1KrB1Kc72jzTnf+6uZX+bd13uNTV16t/JaC6kW/tKBDy66bbhvrlz/Ij8ql1dv+KiMWellbk/Xa2P0xUNm663rt1qKZjtJ5CUaT5fLgjULuI7fKufxqut3/AGjeXOpgMFuZN0e4YxEMLH+ajP41WBTc8PFqzipSflzPRfi/uHS1cF6v7ySiiivoTtCiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKCxCnDqre9B4UmtPRbbfqTXUi5gtUM7EsFBx2JPb9K5sZioYSjOvU2ir/16kzmoRcn0LnGjWUVojRLqF6saORGZZEWSQIAF+7gjeDk8elVrSeSfUbeSDUXmZn1BktZUC+c21AqoB1UDA4PcjnFNu7qSX7RLDey2TFHkV7aNgiNDMdxzjczEH+Hrzxir8MLPqCTSRJNAL9jBPGVi8qCdNwYoByTtjGOGzk844/LKs5VXPEYj4pc2/TTlSV0no3pZ9L9HfwXNzk6kjNcQ22nSXiRwxXsehxx/Zip8tUMmOMnkHnIPK9at3OmXN5Lr1vHFIu+wtPs8CsH3qqIcc9fuSKCPU1s6ZpElrrlvZMlxq96tv9lNvDbG4mu0zkDy+2O7uQCMV0svhDXNGvUu/Fus6D4MW8RhFLqxe9l8pPmbIi2QxBeOrnB+vPPVzSHO3TXM+72+K631e2javZ90EpqO/wDW5zVvpcL+KdSSQbQ+kxQAlclPvA5x0OCOK5m106Vm0p5baU2tjayXNy+M7TvJ2n0bbEOD619E6f8ABfT7WJ3ufGOq3Blxu+zW1pBHJn28tifX71Vrnwf4B8NX8mky+N/sE8sLTvHctb7vLBALthFIALAbiRjPfNcuGzyvQcmvebtbfSykr/8Ak1/kEa/KrtnzhDa3lxYWGmyLtvtZkN/cq5xiHfvJPsXPXphTT1vYBNdeJmtle0t9tppdu3S4YHjj0J3MT6D6V9C6l8Ho4dFvbC1mivXnhZAbgtDKqt1VXIJAOcgZ4PavLdd8B6voFraakLKL7XYqLS10uZ1WC2fI/f5J+cdCcgfdx717WH4goVpclnFt6fNW0fR8qUE3a15S8i1V/r8Py/HU4sRXdjBHo1o8k3iDUAZLqbq9vG5yx9pH5A9F/CmmF7h/+EV0NVuIl+S9njPDbf8Al3Q90HV274qUWzwR3umWd2FkBLaz4hmfAz/EkTHrnBBYdhhQeopNPBc2X9l6XHLZaKQEdiCk97gdD3SP/Z4J7+le/h+evPlpq7dvJafDftCP2Y7z+KyTNoXm+WKv/l0/7dXfqS3dxbXkDaTpcgexRgLq9Q/8fZH/ACzT/pmD1b+IjFOOcqRgcnOBwc0iRxxoFijVAABhRgflTq+rwmFWHi9bye76v+tktkj0qVPk1erYUUUV1GoUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFAAQxGFxzxzW5br5XhEQswT7VJsMsn+rCk+WMj+I7nX5Tx19KwwP3qnjAOfx7VvzQqLHS4XQY8rBLDdyytlIx13sMtnPHl18txZV5cLCn0lJX+Sb/AEOHHyfs+VdWP0q0utTkVrW5mwZQ7LJCqqeDHLAOCRnBIUeuc11uiaTbXNnHqABs9KsnSG41K2jLiMnAVIwOWIBxuznjIwDk4Ys72TxJpXgiz1BDq2sRh7rUZR81vadC+09HlwFC/ebgD71fUPhSLwldfDmxtPCT291oc1uVhkRcmUHcCzA4O8sDuB5DAgjpj8zxtWU9vh6W+7y8+ne55MqivyrcyPCut/DDQ9HH/CPa1pkEJSNpLiVts7+YcIXYjPzHj0zweaxfjV4c1/xH4FvBpWtPBFHZXMR0pUQ/bZnTCfvGxtKk52jqQPSsDRfh/p1rBb2klrY65NpV3dNY3u15Le1ikk3iFUY7Z5EYsd7DCE8AkVmz6xqvjPxPc6L4At01R7J/J1HxJqTO9jZvjmKPbzNMOuxcKvc4rhjFKf7nVrvsc/NdWqaX+877wjL4Y8PeHY3g1CG0vL6K3n1GGS6M4iuBCiuoJyFwV7detco/ga08V/GfxDq+r29vdeHZrO2WGK3uhtvZFdmYTAfMUXI+TO055zWtpvw1sbVvtGveMtb1m7A6m5S0gGR/DFEANvpkt9as33hTSI7UtYXnkyD+Azht2O2c7geM9fwqHOVOTlF3f5feaKmnFJqxpSy6H4K0WcJeMqyzy3SQ3l0Wd5HOSkbP0BIwqjpnHauR0DxdbfEHWtV0jXdFsksUtYZYbeZ1km8xiwlUOPlOzCg7SSCaw7jWNWm+JMXg2e3ivhFpcmpWt9dFZJrCVT5Z8t2yoJzxu4NdZ4R0DwrYaFpM2iQfaJLCKSCC7uDvuEaRszBufvO3UDgduKpQjyty3ewru9o7I4n4j+A7vUdTtBZIpt9qhA5U2+9ANrSrweAvX3614+zweZdBHZxDOsTTQrtt1yD/ABHp0JJPA6Zr61uJlZNkrBIyNmxnXOTwAOeuc8Zya+ffidoWheG5NLhv0Lee880VlbxCOOfBAUSDozMWxkA46+9fScO5tVws/Yp6PZW06N3Xytprd7o6qdZ0nozi2DI7RupDqcEZHHOKSi5eWzKpqslna3F3ciY2UMLSSwod3zDG6QhmYDBIHyk4HGQmPeyxyJIFdk3IeDgkHGeeoNfp+AzCOKjbaS3/AFs7tb6bs9ihXVTTqFFFFeibhRRRQAUUUUAFFFFABRRRQAUUUUAFFFHHcge5OAKACippYYbMIdUv7SwLqGEc7nzPqEAJx/jUYu9CB+bU7yb/AK9tOlOfxfYK4JZphovlUrvyTl+SZi8TSTtzDaKeLzSBkx2Ov3A9fLhiH15c0q30BAS38N3Mz5/5a343H/gKRn+dR/acX8FOb/7dt/6VYX1iPRP7mRMMox549K7jQtJ/tp7GbfILa0szNcXSbVNusZz1J6/LkMAem3+KuWSDWmUSDwlYQLkHN5cyAf8AjzKKvanfNB+z3411b7doxurW3Wwhh0qbeyG5kEYDfMccbj15wa+U4jx0cXThTgrNSXWD3TWyk31POx+Ji6e2q16f5nqXwJ8H6b458C+IfiR4xtBc3HijVFubLzWKNBBbPmAqwOVO4Z4x0xXbwaRqXg9Y/A2j31uvh2WBpocBjeWitIWm+Y8MrEkITlssTyFrp/A2jp4d+EvhrRIIlVbPSoECgfxFAx/VjXI3etRy+KtbuXk3lbv7LGx5wkHyYH/A/MP/AAKvgsVUlJy5Xp/SX4Hk06aSTe5zPxs8R3+h/B0aZ4dn/s641S9ttFjuI+Ps0UzbWI5/unGfc12lteeEfhx4It9GjaDS9I0qJbcF2Cqh3YLMx6s7Hr1JNeN/GzUEufCnh+KNt2fElgcHn/lpU/7QV2Jvhl4mtlDSF7yAbAOpFymeg9OaKNK9OnT2UpO/4Ihy5Zzl1SX6npviLxVYLYi/WyuTaxvi5uI0J+zr/fKkZZfUjOBz0rK0txqPxCitHl8yxl0j7VGqvhHYzkCTI6/LgfStLxrr2naXFFc3l6iwW6PNMxOQsW0ckds9AO+ceted/CkXVkdJh1BPIH9hSELOxXy1e7LrGc9CEI4rKnRi7yfT/L9DVyfMonqX9gaHDqh1JLEfbPK8gTvI7MI927Zknpu5+tclq+mSeH7nUL9A8mh3MR+2FGIaNG+V8Adxu3gjoN3oK3dU8Qx2uq6bYWphuJLy6W3c7sCJWBO4epyMYq06rcp9mnG+GdWjkQ/xKwwR+RNHLbU2fK9Eczf+DI7+G9+361cXszQG2sJLkCUWNuUVcKpPzSsF3GVudzZGOlT+K5LPT/h5fahfPc3kOkWEh8qRfOe5/dhFUnGcs2MsMHkms34fajPffDnTDcTNJNbebYSu3UvBI0RJ/BBXQq8g85HdljZfmI/hj7sPcDn8K0mnfll0ZKjFK8ep80aVe3FzBa3mm6Vp+kXeplZ4hJOZvsy42AYOPmwAqqQdq8k9BUkElszxadaatHcRQRyM8yRAKGH/ACz3KoGzgncSee9W9S8QXPj3WtZ1eHw1puk6YLo20d/eK1vc3EajgSbWGXZCmcctiohFqF/p0kNtaaTpuljy45HuBF8565fc2EHcLk++a+2wmKcVGV0pJd1p5NuTaSvpFK8t9DfDVHyxaeq2/q+iIgysuQDyOMmlpzF5d06wxJbhhDE6lRv2qNx2qSFJJBAGODTa+9wuIjiKUasNme9TmpxUkFFFFdBYUUUUAFFFFABRRRQAUUUUAFKMZ5IA75OBSUAZOM498ZoBmjdWNpeXmo+IkuWMTMJLlzGzzQk4URlFGSOMLjgjk1m/b7TcFttEvpyBu33c6W4I/wB0bmFW7S9AgFrK10m5g8ctq2yWOQZUYz98EMRg+tad6WFxeJHaQXBtQI5dWttk7RSA/M0ltxtxyOmeM818XVxNXL6v1So5ciXucrSbSS3drvV2918391vU8ycpUnyXdulv1MiCXX7r57DT9Kt19Ut2uCPxc4z+FNnmuYeNV8cS23rb28qxv+CQKD+BNTaho9ytu1/r+uTy2BIKzu7LEcgkBYkAOSM/LjtWfbPawkR6DoDz7j8k94piQ+4iTLH/AIER9KuPs8SrwUZel6jXrKdoxfk9SHaWm/3yf6JDYrXRru5DWfhzUNanyNs98wjX6nfvcflWv4itYz+zp4vEsWmQ31tdadm3sJTJtj+0jlySeR0/E1nag0n2j7L4h12SR+p0jTNquuP7wT5UH++fwrr/AAVpGn6x4Y8R+GLvSbHRxq+nOmn2rSA3E8i/OHI43cqvIGOe9eXmM3Gg5p3imtndb+XLB9dFGVrbo5cTDng4L+vu0/M+wbHauh6fNsBT7NCwwfvDy1r5s1i/n0rxJq9hcAiRNRuic9w0zsD+IIr3rwHenU/hP4eu3O2QWMUEg3ZG5BsYfhivFvjHpUlj8Q21Iq/2fU0EqsmNodflkXI6EEA/ia+I0k9Nmc6VnZnlnxD1L7Xpvh+Pdz/wkNiQP+2orZ+L/iXU9Hj8Rz6TePa3UV+qLKAGwGnVTwQR0J7VyHjJ1Mfh0NtUrr1kdw4H+tHJrV+LkLa1J4ltNKkjnlk1AFMuAHC3CsSCfQKeld1OMbUuba7/ADRy1L3qW3svyZ6v8TfDehaboWnu9tI0Uk+CN7Eq4G5WUk5DA85rj/hzfSeKPF+reG9YvJZv7LhLvcRqA8xMg2OeMcoRnH8VbvxT8deGtX0zTodO1JJlilZpGCEHO3AVV6ueT0Fc/wDA+0nh+KGvandxGGbUbHzxA7BjGgl2ICRxnC8/WsYQ/dyv8jWb9+PL8zv9U8ISWXizw9dad588EGoLJdBzlkG1sOfzrqUX/SVHXHSrcvBIBPpXMeLtbk0DwfqF/bIXv/L8qyjHWW4kPlwoP+BMD7BTWFnKyNUuW7OY+FShvh3Jc8lLvVdQuYvdHuHwfyGfxrrZpEt0lllk2xxIXaT+4q/Mx9/lBqn4d0aHwz4P07w/E8cj6fapDww3EgfM5HbLGo9f8SaP4N0CTxFrxmbT7dlE6QruaUMCNij1bIFXUvUqNpbsmPuRSZ4frHjE/ETxDPqNl4WfUNHtna20SSVjHO0QI3GcjORw23C7sNt5FZ1xb2lrebtX0qVp1QzW9jZSqwgz227AAPV2O7608pezwDUPEmmDRbG4kKQJp4xdRwYysUm1SSwG0c7evXFP09lZ7ZPDtxcWEhyrSX6SSLuPTATchHu2PevrcFz06MXTvaL6NtL5rmjHzbV/JHRRuop9v67NL5kJa2aJ7wwTaXZQIBHGwjKNIxAO5lbczdMcYAz0zTucKDw3U+/0q5LFdI0V1q12utraytELa1jjunZyOQuziPP944A+vFUYt5toWlZDKVAfYeC3fHtX1uRVlJVIJ3Sd9HzLX+9ZXfV6aaI9XBy+KP8AwfxH0UUV7x2hRRRQAUUUUAFFFFABRRRQAUdaKKAA8nLZbnJ6c/n/ADrWsrh7mK5lMQn1Tyx9murPYl1tPDAb8I5AGM8N/OsnvmmtHFJhJANpP459R715uZ5bDHUvZvR9H92nmnazWzMa1FVY26m4jxw3Ml3cag/9p3ESsqbI7bUZQGCASRufJlQ4bk4OFzknFSPp/wDbhmtNMaXRMZeSKNWieRTwFkLYdPrGWU+tVrS5F/qNrZX0srF1EDLJAk8Nwo4AYn5lYjjOTyahtro3tokd7qFlZ2USiJ44Z2ihgPJVfJnXDMTwNpB6dMV+b4rDYjCTcfhatdNe7a75dLJS20SWj2s9DxqinTbT0/Ihk03U9DvxpOi6P9mmUgf2hcRoybupMSHIb/ffp6U3w9ejT/Fcep6JFHq97BJ59zrF5ITGm37xRj97GT8x+Ue/GOo03U4NWtHsb3S5JNLMBWRnHmBhj5gSjMDz/D1qHUfB9nq9tEunXQTS1+aaySMr55B+XOccDHCkcEVpRz6FVunjlyyas5a2d+7Xwr+7G13vKzKjWUt/6/yR9C+F/FFp/wAIVHPo2k3mu2epOZoo7EKVXd97OcYXPfjGfxrk/D/ws1SeHxUNdt4dFiv70TWWkW5WWKOdRgXYcMdjSr8rp6oCck5rh/h7401Lw7PbabrVsumRTTn7JCmC8QHXeR97ry3TJr3vUtQi1TwZeCHWv7JLwbReJj/R+eXGeuCcY9/cV4Vek8NN01s9nvpv0ur9/M5KlN8yb6Hyx448LatBDe6JcQ+Xq1vKl1aPOBtE8bBkI9mxg/UV9E+CfFOg+PfBUGv2VrbRz8Q3ti8KiS0nxh4nGODkEgj7wxzXmHg6x1zxR4gn8O6jqH/CU+HoEdX166Rkkt5hj5YpDzJuOcpyF6Z7VV1LwLqPhjxqLnwl4rgg1qT5I44LmOOaZOySxN8sn3futzwcGnJK3s5PzT/zMIt83Ol5Nf5HU/FWe3n0+HR9N0iVr1JBJLNb2n3FAwAWA6nI4FcL4Pu7rwt4ouNVuNA1C5Wex+xiGJNpBEm8tnHAxXfaT4s+KUI8jWfCtpcsDgSwu1sSfUrkgfhWb4qv/iFe6dILiXTvD2mHAkklutudxCgFupySBgVmnb3UzVq6u0QL8ZLO41650qDw5qBuILcXLN58ZBUsQeCOMY5PoR3plla+JfFsyeIr28jsIbcltKtzF5kaSkFfOKt1AGQC3XLHuKxtK8HWVv4TvfGOgSxeI9bMD2UWxSkJaN8eUUbBIDDJDYBwO3XU0zWfFXh/xVo2h+Krxbmz1MSLDKo3vBMV3om4AAqMOo44wKpxu7w0t+m5PP8Azdf12MeXw54isb+CLUlmF9dTuYNd04NJLbyyPuAdcgNCucYO3AUZUgnFP4s+K4bzTdU+FFrYm81u7t7eYTM4jSMKQ+9ezyNzhVxwTmuy+IXi5PCHw91TXhFJci3lgt3jjfYfMlJCx57Ejcx/u/UgV47qs1v4k8Wn4haveSGa+to7ZIdFiYG1WNAFT5sfMOOWxnGQa68HSlWkpSWnS3V+n6IcYXlyRf8Aww3SNPmsLG0gtNPOi30W1JL6+UmNio5LbGUKSQSQ4ZOevanal5v2aI+Ib631SBydgi3p5mTycW4KMR23qD70s4sRZo89jd+JNPRSiPMy5hc9sv8AMhz1ByCeRxTonjhlVvDNqqS8SS21xOY2Y918sDa49xz9K+h9m5XqNX1snZ6W6KcmnH0lG3RHco6bfn/wFf1RXiPh+NklsbeT7WsgS3W+/wBBX2bzFDY/3PlP8qTZdozi+eNrnzH85o+MvuO4Y7DP8quW9xqGoypbDT4LC8lnC/arK283YvQbo36DJGWFZ1tGsMDRif7QfNcvNv3b33NvYnuS2T/kV9PlamsTJVea/Kvite3ly+7b8b76HoYeMlN37dbfoS0UUV9CdoUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAHOOGUfU4z+VTNf3P8AZ32Wea4uIAQyF1jmeIj+6JhtIxkYJX2NQ0EuPud+tcmLwNHFxUa0b22fVen9W7pmVWlGorSLhs21X7FZWRElpKFZkOk25EMuMO0xVxhuO3GMYz1qxbahfJeQy20F1pml2SiTZd23klvlyVkb7TyzkfKGGFJx2NYzW1sZ45niDSI25WwPlPqD1BpyFoftJMdrL55DZFrGJA4OQ+7BBYe4r43H8L10n7J869Enq9X0Tdtvys9PLrZfNO8dTrbTxnFJYSXl/bRAGbZbIjRM0nOSuI5JMlRjPCjnoTXXaH4i0y0jOgSCOS2uYl/4lN0PklDAkqAxyCACSODx0AxXk01+ptbNr2C8Ig+SWLzGdJVzniOLaAx5GTx0pTfWrahqaDVEM15C2JZItisWwWDIgB+7wCzHnGeK+VrZBWpN2jKP323tp8te+9jjlCcdJI+m7LxbpEfh0WujQWtnJAnlWttIDFbqwHyrkAgD1IrzCDwNqVz47v4NRils9V1J01vTfEelsZ7fTp40CMshOAxJJC57Fq5TSPGlja6XYWV3PGqxjy5CZMeVjozALjHsvTj0roLLx9obXHkaPra27BcAYcCV/dnwpPtxn1rgjTxVFy5qb9Unt3vr669CJUlNK57g8hWMIz7yoALf3jjk/iea4/x94dm8XeF/7MtbuK1vIZkuraaVjsjkQ7kYgdcMA2P8a5ST4j3C65/Zz3baepjXE+pRBPObH8I6bfxzVG/+Ilxb+IJ7S+lvtNsEGIr141JuCBywZVKhewHJqqeHxDkuWm777dP8vw8y3BtWN3wtoes+EPEWrrftato2oNFdI6yY23QUI4SM/NtYY+hjHXdT9R8feH7PVtRsn1C2e50+NxNAJAJ3mCkrEBjCZbaGZiCBngdRwM/inxPN4ludft0F9Zq4+xpp0qTfZUA4bDDO8nJJ4Gc9BiuVgls7SSYWOtX+lmZ2llivLZZEZnOWJcqxPJPevUw+UVa79pVat5Xf3uKaXzZVLDtLy/r5Fmxk8Sa1oJ0nxPrdlLqtvctPJptzbo8aIuclVKYLLgn5dzMr/wCzVsXb3c02paTr+jrCsSte2iiF4o1BwNx2BihPPPKk4qwZNSvdNFzaXGlXt/bupaSEbmkTopCowZSo9vukd6inmkjRNVj0cx36EvcxRymPbnjcisMGNs4YHoeOmK7MNSsrQinZ2t7rXNvZ2afK94yteL030NadJRWmv4/qMWXVNRmkvNG8RwuHy9xZR3FrJ5aKSRuOPmj54YjPZgDg09l1HUS89vq81ncBvMEVtdo0DE8fuyGLI3+wc47GoMaVMr6xawX9nNG5L29uqyyQrj/WK3dc8cdAcMDUCWHh7Wp4kiS2gv2GGjnsjCkgHRlJ4U/7OcZ6V3+xpxkuZJKO7dNtp9p68rVrWlq/Pq9XFKyf5P8AHUmvY7xbBoPFF3cJapG5E8t2Y5M7TjdgkygnAw2Tz1HSsyBUS1jSKHy4tg2DbjaMdPw6YoupNI8sW7y2up6lHIqQlYG82EAncHkYD5QOx5BwOlSd27/N19a+myOioqpUikk3a0VaOnVX1s0/JJ7K+r7cKl70lb5f5hRRRXvnYFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUcFeUVvrRRQAgwP4EH/Ac0Pl4yrEFP7uOPy7/jS0UMGTQXd3bxfZg0V3ZHk2V4C0ef8AZPVPqD+BqxaOrxNHo149hIx+fTb4iSN/+ubNlW+nytVGkdY2j2lAcnlSOD7/AFryMTk9GprSSi97W92/p0fnG0vM554eL+H/AIH+a+TLEyWCXWb/AE240m9Bx59orKgP+0mfMX8C1WT/AGwlmZY7my1yzU8yyL5oX23rtdT/AL2fpVWO9ngjEUqi9tR0glPzqP8ApnJ95focj0xT4bS2uJxNolxJb3g5MJbyZ/8AdDdJB7c15FXDSoyTrK1uru18qitOH/b112uc7puL10/rv/mJb3WnQ3cV8tveaVcxHIdVFzGp+q7X2+2xq0lhvYrv+0/DV491YyjLw28rXECk8vGyMCce3Bwfas1rq4WYxalp6XBXqYgLa4T6/wAL/iBVvT49Nu3ls4brMVxgSQyZgnQg8SKARyp/unkZrlzCiof7RVjdpWtNc0XG/Sas7rePM79FuRUjb3pfj/mhbu6uLe4i1KxsbD7OXKqp3Qz28mclGZDg9DglSGXPXnDJF0u+sp71bG7t3jJeSxttkwjXvImShK+uMFfTvSPd6zpd3NpmoTteQxuI57a6Acumfl2yDDjg5DZyM029uhp2o/atL0iORZUeS2n+1/KAw2/MpXO4ZwRnrU06NWioulzc8l7koy5oyitbPmtr522fMvtIFzQV1e726plKa+kv70OkVwsEcKxh7sKsspBPzEKT0BUDJzxk0lMiEiW0UcjAsF2nYOPfGeQKfX2eFw8cPSjSjsv69PktF00PQpx5YpBRRRW5YUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFFFFABTXiSZD5wB/2RkZ9yfX3FOooaurMPUsJqM7QiHUYRqNuOglbEy/7snb6HIpW0+z1JQLKUXYHWznGydPcKeG/3lNVqZJGshXcqtgdeRg+2Of1rzHl7pa4SXL/desH8un/btjB0rfB93Q2BfX48PT27tClxYxmcC7g83MQOGRifmyCRj1GR2FZEkt5cXaSXTW6pDGYoobaLy1UE53Hk5Y8Z+gpJjfz2q2cusahJa5G6FpvlbnOCcbiM9ixHtTu+fWufL8rVGrKrOCWt0k20naztolr6aX0M6VC0nKSt21Fooor2zrCiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigD/9k=',
  telebirr: 'data:image/jpeg;base64,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',
  mpesa: 'data:image/jpeg;base64,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'
};
