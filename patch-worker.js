// Usage:  node patch-worker.js worker.js     (worker.js = a copy of Aman's worker)
// Makes the 4 Anbesa edits automatically and writes  worker.anbesa.js
const fs = require('fs');
const src = process.argv[2];
if (!src) { console.log('Usage: node patch-worker.js worker.js'); process.exit(1); }
let s = fs.readFileSync(src, 'utf8');
const edits = [
  ['TOTAL = 600', 'TOTAL = 400'],
  ["const BANKS = { telebirr: 'TELEBIRR', boa: 'BOA', mpesa: 'M-PESA', ebirr: 'E-BIRR' };",
   "const BANKS = { cbe: 'CBE', telebirr: 'TELEBIRR', boa: 'BOA' };"],
  ["const BANK_DEF = { telebirr: { a: '0958828304', h: 'AMANUEL' }, boa: { a: '266199511', h: 'AMANUEL YISMAH' }, mpesa: { a: '0706577754', h: 'AMANUEL' }, ebirr: { a: '0958828304', h: 'AMANUEL' } };",
   "const BANK_DEF = { cbe: { a: '1000734517023', h: 'kidus' }, telebirr: { a: '0900060528', h: 'kidus' }, boa: { a: '243456916', h: 'kidus' } };"],
  ["const acctText = (env, k) => { const x = ACC[k] || { a: '', h: '' }; return (k === 'telebirr' ?",
   "const acctText = (env, k) => { const x = ACC[k] || { a: '', h: '' }; return (k === 'cbe' ? '🏦 ንግድ ባንክ (CBE): ' : k === 'telebirr' ?"],
];
let ok = true;
for (const [a, b] of edits) {
  if (!s.includes(a)) { console.log('NOT FOUND (already patched or different version): ' + a.slice(0, 60) + '...'); ok = false; continue; }
  s = s.split(a).join(b);
}
s = s.split('አማን ቢንጎ').join('አንበሳ Bingo');
fs.writeFileSync('worker.anbesa.js', s);
console.log(ok ? 'Done: worker.anbesa.js is ready (all 4 edits applied).' : 'Written with warnings - check the lines above.');
