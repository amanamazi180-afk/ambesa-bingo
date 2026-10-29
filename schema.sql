-- Base tables for the Anbesa database (the Worker creates all the other tables by itself).
CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY, name TEXT, phone TEXT UNIQUE, balance INTEGER NOT NULL DEFAULT 0 CHECK(balance>=0), bonus_c INTEGER NOT NULL DEFAULT 0 CHECK(bonus_c>=0), bonus_period INTEGER NOT NULL DEFAULT 0, auto_off INTEGER DEFAULT 0, created_ts INTEGER);
CREATE TABLE IF NOT EXISTS rounds(id INTEGER PRIMARY KEY AUTOINCREMENT, start_ts INTEGER, seed INTEGER, status TEXT, stake_c INTEGER, ended_ts INTEGER DEFAULT 0, called_n INTEGER DEFAULT 0, winners TEXT);
CREATE TABLE IF NOT EXISTS picks(round_id INTEGER, cartela INTEGER, user_id INTEGER, bonus_c INTEGER DEFAULT 0, PRIMARY KEY(round_id,cartela));
CREATE TABLE IF NOT EXISTS deposits(id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, txid TEXT UNIQUE, amount_c INTEGER, method TEXT, status TEXT, note TEXT, ts INTEGER);
CREATE TABLE IF NOT EXISTS withdrawals(id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, amount_c INTEGER, method TEXT, account TEXT, status TEXT, ts INTEGER);
CREATE TABLE IF NOT EXISTS sms_log(txid TEXT PRIMARY KEY, amount_c INTEGER, raw TEXT, claimed INTEGER DEFAULT 0, ts INTEGER);
