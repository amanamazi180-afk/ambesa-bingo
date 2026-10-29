// Runs at deploy time:  node patch-worker.js worker.js   ->  writes worker.anbesa.js
// worker.js = Aman's server file, copied UNCHANGED. This script turns it into the Anbesa server.
// If any expected line is missing it stops with an error, so the wrong server can never be deployed silently.
const fs = require('fs');
const src = process.argv[2] || 'worker.js';
let s = fs.readFileSync(src, 'utf8'), bad = 0;
const rep = (name, re, to) => { if (!re.test(s)) { console.error('NOT FOUND: ' + name); bad++; return } s = s.replace(re, to) };
rep('400 cartelas', /\bTOTAL = 600\b/, 'TOTAL = 400');
rep('deposit banks', /const BANKS = \{[^}]*\};/, "const BANKS = { cbe: 'CBE', telebirr: 'TELEBIRR', boa: 'BOA' };");
rep('bank accounts', /const BANK_DEF = \{.*?\} \};/, "const BANK_DEF = { cbe: { a: '1000734517023', h: 'kidus' }, telebirr: { a: '0900060528', h: 'kidus' }, boa: { a: '243456916', h: 'kidus' } };");
rep('CBE label', /\(k === 'telebirr' \? /, "(k === 'cbe' ? '🏦 ንግድ ባንክ (CBE): ' : k === 'telebirr' ? ");
rep('admin page link', /'https:\/\/amanamazi180-afk\.github\.io\/Aman-bingo\/admin\.html'/, "((env.GAME_URL || '').replace(/\\/?$/, '/') + 'admin.html')");
rep('invite link default', /env\.BOT_USERNAME \|\| 'Amanbingo2bot'/, "env.BOT_USERNAME || ''");
s = s.split('አማን ቢንጎ').join('አንበሳ Bingo');
s = s.replace('// Aman Bingo server', '// Anbesa Bingo server (made from Aman by patch-worker.js)');
if (bad) { console.error(bad + ' edit(s) failed - nothing written.'); process.exit(1) }
fs.writeFileSync('worker.anbesa.js', s);
console.log('OK: worker.anbesa.js written (400 cartelas, CBE/Telebirr/BOA deposits, Anbesa texts).');
