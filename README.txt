አንበሳ Bingo - fast & easy setup (3 steps)

1) WORKER (server)
   - Put Aman's worker.js next to patch-worker.js and run:   node patch-worker.js worker.js
   - Deploy the new file worker.anbesa.js as a NEW Worker (its own D1 database, bot token, TG_SECRET, GAME_URL).

2) GAME PAGE
   - Open public/index.html and change the ONE line:   "https://YOUR-WORKER.workers.dev"   to your Worker address.
   - Upload the whole "public" folder to GitHub Pages (or any static host).
     index.html, sw.js, 1.m4a ... 75.m4a, bingo.m4a must stay together.


What is faster now: the heavy lion drawing is gone,
the 400-card lobby only repaints the cards that changed, the voices are saved on the phone after the first time so every call starts instantly,
and the connection to your Worker is opened early.
