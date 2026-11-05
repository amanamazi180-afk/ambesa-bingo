/* topbar.js - the shared top bar for every game: logo, balance (**** / eye / refresh), Deposit and menu. Same look as the lobby. */
(function () {
  if (window.__tb) return; window.__tb = 1;
  var API = (new URLSearchParams(location.search).get('api') || 'https://ambesa-bingo.belssedamanamanuelyismaw.workers.dev').replace(/\/$/, '');
  var tg = window.Telegram && Telegram.WebApp, flow = !!document.querySelector('.host'), bal = null, show = false;
  try { show = localStorage.getItem('tb_show') === '1'; } catch (e) { }
  var css = '#tb{display:flex;align-items:center;gap:8px;box-sizing:border-box;height:52px;padding:6px 10px;background:#0c0805;border-bottom:1px solid #3b2a17;font:700 14px system-ui,sans-serif;color:#fbf3e4}' +
    (flow ? '.host{display:none!important}' : '#tb{position:fixed;top:0;left:0;right:0;z-index:8}.s{top:52px!important}') +
    '#tb .lg{font:900 15px system-ui;background:linear-gradient(90deg,#ffe08a,#f2b632,#f97316);-webkit-background-clip:text;color:transparent;flex:none}' +
    '#tb .bl{flex:1;min-width:0;display:flex;align-items:center;gap:6px;background:#17100a;border:1px solid #3b2a17;border-radius:22px;padding:7px 12px;color:#f2b632;font-weight:800}' +
    '#tb .bl span{flex:1;white-space:nowrap;overflow:hidden}#tb button{border:0;background:none;color:#b39b7a;font-size:17px;padding:0 2px;cursor:pointer}' +
    '#tb .dp{background:#f2b632;color:#241500;border-radius:20px;padding:9px 14px;font:900 14px system-ui;flex:none}' +
    '#tb .mn{background:#17100a;border:1px solid #3b2a17;border-radius:14px;color:#fbf3e4;padding:8px 11px;flex:none}';
  var st = document.createElement('style'); st.textContent = css; document.head.appendChild(st);
  var bar = document.createElement('div'); bar.id = 'tb';
  bar.innerHTML = '<div class="lg">አምበሳ</div><div class="bl"><span id="tbv">****</span><button id="tbe">🙈</button><button id="tbr">⟳</button></div><button class="dp" id="tbd">Deposit</button><button class="mn" id="tbm">☰</button>';
  flow ? document.body.insertBefore(bar, document.body.firstChild) : document.body.appendChild(bar);
  var $ = function (i) { return document.getElementById(i); };
  function paint() { $('tbv').textContent = show && bal != null ? bal.toFixed(2) + ' ETB' : '****'; $('tbe').textContent = show ? '👁' : '🙈'; }
  function initData() { var d = tg && tg.initData || ''; if (!d) { try { d = new URLSearchParams(location.hash.slice(1)).get('tgWebAppData') || ''; } catch (e) { } } return d; }
  function load() { fetch(API + '/api/me', { headers: { 'x-init-data': initData() }, cache: 'no-store' }).then(function (r) { return r.json(); }).then(function (d) { if (typeof d.balance === 'number') { bal = d.balance; paint(); } }).catch(function () { }); }
  $('tbe').onclick = function () { show = !show; try { localStorage.setItem('tb_show', show ? '1' : '0'); } catch (e) { } paint(); };
  $('tbr').onclick = load;
  $('tbd').onclick = function () { var d = document.getElementById('dep'); if (d) d.click(); else location.href = 'aviator.html#wallet'; }; // inside Aviator the wallet opens directly
  $('tbm').onclick = function () { location.href = 'index.html'; };
  paint(); load(); setInterval(function () { if (!document.hidden) load(); }, 20000);
})();
