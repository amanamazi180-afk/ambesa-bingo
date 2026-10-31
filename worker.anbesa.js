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
// ACCOUNT PICTURES: this file has no built-in logo pictures (IMG_DEF at the bottom is empty). Upload them in Admin > Accounts; pictures already saved there are kept.
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

// Default account pictures: none built in. Upload a picture per bank in Admin > Accounts (pictures already saved there are kept).
const IMG_DEF = {};
