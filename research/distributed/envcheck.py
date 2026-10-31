"""The environment models of core/system.ts against the stacks they describe: each claim a model makes, run on the real
thing (PostgreSQL, Redis, an HTTP client with retries), printed as CHECKED or DIFFERS. The models over-approximate (a
proof under one holds of every run the stack allows); each check here is a run the model says the stack may take, or a
run the model says it refuses, and whether the stack takes it.

    python3 envcheck.py --pg 'dbname=postgres user=postgres host=/tmp' --redis redis://localhost:6379/0
"""
import argparse
import http.server
import json
import socket
import threading
import time

import psycopg
import redis as redis_py
import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

RESULTS = []


def check(name, model, ok, detail):
    RESULTS.append({"check": name, "model": model, "ok": ok, "detail": detail})
    print(f"{'CHECKED' if ok else 'DIFFERS'} | {model} | {name} | {detail}")


def pg(dsn, level):
    c = psycopg.connect(dsn, autocommit=False)
    c.execute(f"SET SESSION CHARACTERISTICS AS TRANSACTION ISOLATION LEVEL {level}")
    c.commit()
    return c


def reset(dsn, rows):
    with psycopg.connect(dsn, autocommit=True) as c:
        c.execute("DROP TABLE IF EXISTS acct")
        c.execute("CREATE TABLE acct (id int PRIMARY KEY, bal int NOT NULL)")
        for i, b in rows:
            c.execute("INSERT INTO acct VALUES (%s, %s)", (i, b))


def bal(dsn, i):
    with psycopg.connect(dsn, autocommit=True) as c:
        return c.execute("SELECT bal FROM acct WHERE id = %s", (i,)).fetchone()[0]


def postgres(dsn):
    # Read committed: two read-modify-writes computed in the application, interleaved; the second overwrites the first.
    reset(dsn, [(1, 100)])
    a, b = pg(dsn, "READ COMMITTED"), pg(dsn, "READ COMMITTED")
    va = a.execute("SELECT bal FROM acct WHERE id = 1").fetchone()[0]
    vb = b.execute("SELECT bal FROM acct WHERE id = 1").fetchone()[0]
    a.execute("UPDATE acct SET bal = %s WHERE id = 1", (va + 10,)); a.commit()
    b.execute("UPDATE acct SET bal = %s WHERE id = 1", (vb + 20,)); b.commit()
    got = bal(dsn, 1)
    check("two deposits read before either commits: one is lost", "read committed", got == 120, f"balance {got} after +10 and +20 on 100 (120: the +10 lost)")
    # Read committed: each statement sees what committed before it (a read after another's commit sees it).
    reset(dsn, [(1, 100)])
    a, b = pg(dsn, "READ COMMITTED"), pg(dsn, "READ COMMITTED")
    a.execute("SELECT bal FROM acct WHERE id = 1")
    b.execute("UPDATE acct SET bal = 150 WHERE id = 1"); b.commit()
    seen = a.execute("SELECT bal FROM acct WHERE id = 1").fetchone()[0]; a.commit()
    check("a second read in one transaction sees a commit made between", "read committed", seen == 150, f"second read {seen} (150: read at its own step)")
    # Read committed: UPDATE ... SET bal = bal + k re-reads the row it waited for: atomic, no lost update.
    reset(dsn, [(1, 100)])
    a, b = pg(dsn, "READ COMMITTED"), pg(dsn, "READ COMMITTED")
    a.execute("UPDATE acct SET bal = bal + 10 WHERE id = 1")
    t = threading.Thread(target=lambda: (b.execute("UPDATE acct SET bal = bal + 20 WHERE id = 1"), b.commit()))
    t.start(); time.sleep(0.3); a.commit(); t.join()
    got = bal(dsn, 1)
    check("an increment in the statement itself waits and re-reads", "atomic", got == 130, f"balance {got} (130: the statement is one atomic step)")
    # Repeatable read (snapshot): the same interleaving; the second commit is refused.
    reset(dsn, [(1, 100)])
    a, b = pg(dsn, "REPEATABLE READ"), pg(dsn, "REPEATABLE READ")
    va = a.execute("SELECT bal FROM acct WHERE id = 1").fetchone()[0]
    vb = b.execute("SELECT bal FROM acct WHERE id = 1").fetchone()[0]
    a.execute("UPDATE acct SET bal = %s WHERE id = 1", (va + 10,)); a.commit()
    try:
        b.execute("UPDATE acct SET bal = %s WHERE id = 1", (vb + 20,)); b.commit(); err = None
    except psycopg.errors.SerializationFailure as e:
        err = str(e).splitlines()[0]; b.rollback()
    got = bal(dsn, 1)
    check("the second writer of a cell that moved is refused", "snapshot", err is not None and got == 110, f"balance {got}, the second: {err}")
    # Repeatable read: write skew (each reads both rows, writes its own) commits both.
    reset(dsn, [(1, 50), (2, 50)])
    a, b = pg(dsn, "REPEATABLE READ"), pg(dsn, "REPEATABLE READ")
    sa = a.execute("SELECT sum(bal) FROM acct").fetchone()[0]
    sb = b.execute("SELECT sum(bal) FROM acct").fetchone()[0]
    a.execute("UPDATE acct SET bal = bal - 80 WHERE id = 1 AND %s >= 80", (sa,)); a.commit()
    try:
        b.execute("UPDATE acct SET bal = bal - 80 WHERE id = 2 AND %s >= 80", (sb,)); b.commit(); err = None
    except psycopg.errors.SerializationFailure as e:
        err = str(e).splitlines()[0]; b.rollback()
    total = bal(dsn, 1) + bal(dsn, 2)
    check("write skew: two writers of different cells both commit", "snapshot", err is None and total == -60, f"total {total} (-60: both withdrew against the same snapshot)")
    # Serializable: the same write skew; one is refused.
    reset(dsn, [(1, 50), (2, 50)])
    a, b = pg(dsn, "SERIALIZABLE"), pg(dsn, "SERIALIZABLE")
    sa = a.execute("SELECT sum(bal) FROM acct").fetchone()[0]
    sb = b.execute("SELECT sum(bal) FROM acct").fetchone()[0]
    errs = []
    for c, i, s in [(a, 1, sa), (b, 2, sb)]:
        try:
            c.execute("UPDATE acct SET bal = bal - 80 WHERE id = %s AND %s >= 80", (i, s)); c.commit()
        except psycopg.errors.SerializationFailure as e:
            errs.append(str(e).splitlines()[0]); c.rollback()
    total = bal(dsn, 1) + bal(dsn, 2)
    check("serializable refuses the write skew", "atomic", len(errs) == 1 and total == 20, f"total {total}, refused: {errs}")


def redis_checks(url):
    r = redis_py.Redis.from_url(url)
    r.flushdb()
    # A TTL lapses: the key is gone.
    r.set("lease", "a", nx=True, ex=1)
    time.sleep(1.3)
    check("SET NX EX: the key is gone once its TTL passes", "keys expire", r.get("lease") is None, "GET after 1.3 s of a 1 s TTL")
    # Keys expire at their time (TTL): a key set with PX is there before its time and gone after; under noeviction a
    # write past maxmemory is refused (OOM) and the key with a TTL kept.
    r.flushdb()
    r.set("lease", "a", nx=True, px=1500)
    time.sleep(1.0)
    before = r.get("lease") == b"a" and not r.set("lease", "b", nx=True, px=1500)
    time.sleep(0.8)
    check("SET NX PX: the key is there before its time (and refuses a second SET NX), gone after", "keys expire at their time", before and r.get("lease") is None,
          f"at 1.0 s of 1.5 s: {'there' if before else 'gone'}; at 1.8 s: {'gone' if r.get('lease') is None else 'there'}")
    r.flushdb()
    r.config_set("maxmemory-policy", "noeviction")
    r.config_set("maxmemory", str(int(r.info("memory")["used_memory"]) + 2_000_000))
    r.set("inflight", "token", nx=True, px=30_000)
    refused = None
    try:
        for i in range(6000):
            r.set(f"pad:{i}", "x" * 1000, ex=600)
    except redis_py.exceptions.ResponseError as e:
        refused = str(e).split("\n")[0][:60]
    kept = r.get("inflight") == b"token"
    r.config_set("maxmemory", "0")
    r.config_set("maxmemory-policy", "noeviction")
    check("noeviction: a write past maxmemory is refused, the key with a TTL kept", "keys expire at their time", bool(refused) and kept,
          f"refused: {refused or 'no'}; in-flight key {'kept' if kept else 'gone'}")
    # Eviction under volatile-lru: a key with a 30 s TTL evicted long before it.
    r.flushdb()
    r.config_set("maxmemory-policy", "volatile-lru")
    r.config_set("maxmemory", str(int(r.info("memory")["used_memory"]) + 2_000_000))
    r.set("inflight", "token", nx=True, ex=30)
    pad = "x" * 1000
    for i in range(6000):
        r.set(f"pad:{i}", pad, ex=600)
    gone = r.get("inflight") is None
    r.config_set("maxmemory", "0")
    check("volatile-lru evicts a key with a 30 s TTL under memory pressure", "keys expire", gone, f"in-flight key {'evicted' if gone else 'kept'} after 6 MB of writes over a 2 MB budget")
    r.flushdb()
    # A call that raises after Redis ran it: the request reaches the server, the reply is held past the client's timeout
    # (a proxy between them that delays what the server sends back: a reply lost to the network).
    host, port = r.connection_pool.connection_kwargs["host"], r.connection_pool.connection_kwargs["port"]
    lag = socket.socket(); lag.bind(("127.0.0.1", 0)); lag.listen(1)

    lagging = threading.Event()

    def pump(src, dst, lags):
        try:
            while (b := src.recv(65536)):
                if lags and lagging.is_set():
                    time.sleep(0.5)
                dst.sendall(b)
        except OSError:
            pass

    def proxy():
        c, _ = lag.accept()
        s = socket.create_connection((host, port))
        threading.Thread(target=pump, args=(c, s, False), daemon=True).start()
        pump(s, c, True)

    threading.Thread(target=proxy, daemon=True).start()
    slow = redis_py.Redis(host="127.0.0.1", port=lag.getsockname()[1], db=r.connection_pool.connection_kwargs.get("db", 0), socket_timeout=0.2)
    slow.ping()  # the connection made (its handshake answered), then the replies held
    lagging.set()
    try:
        slow.set("k", "v", nx=True, ex=30); raised = None
    except redis_py.exceptions.TimeoutError as e:
        raised = repr(e)
    applied = r.get("k") is not None
    check("a SET whose reply timed out was applied", "store calls fail", raised is not None and applied, f"raised {raised}; applied {applied}")
    # At-least-once: a stream entry read by one consumer and not acknowledged is claimed and read again by another.
    r.flushdb()
    r.xgroup_create("jobs", "g", id="0", mkstream=True)
    r.xadd("jobs", {"charge": "1"})
    first = r.xreadgroup("g", "a", {"jobs": ">"}, count=1)
    time.sleep(0.05)
    _, claimed, _ = r.xautoclaim("jobs", "g", "b", min_idle_time=10, start_id="0-0")
    same = bool(first) and bool(claimed) and first[0][1][0][0] == claimed[0][0]
    check("a stream entry not acknowledged is delivered again (XAUTOCLAIM)", "at-least-once delivery", same, f"read by a, then claimed by b: {same}")


def http_retry():
    applied = []

    class H(http.server.BaseHTTPRequestHandler):
        def do_POST(self):
            n = int(self.headers.get("content-length", 0))
            applied.append(json.loads(self.rfile.read(n)))
            time.sleep(0.5)  # applied, then slower than the client waits
            self.send_response(200); self.end_headers(); self.wfile.write(b"ok")

        def log_message(self, *a):
            pass

    srv = http.server.ThreadingHTTPServer(("127.0.0.1", 0), H)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    s = requests.Session()
    s.mount("http://", HTTPAdapter(max_retries=Retry(total=2, read=2, allowed_methods=None, backoff_factor=0)))
    try:
        s.post(f"http://127.0.0.1:{srv.server_port}/charge", json={"amount": 5}, timeout=0.2); outcome = "answered"
    except requests.exceptions.RequestException as e:
        outcome = type(e).__name__
    time.sleep(0.8)
    srv.shutdown()
    check("a POST retried on a read timeout is applied once per try", "a retrying client", len(applied) == 3, f"one request, applied {len(applied)} times; the client saw {outcome}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pg")
    ap.add_argument("--redis", required=True)
    ap.add_argument("--json")
    a = ap.parse_args()
    if a.pg:
        postgres(a.pg)
    redis_checks(a.redis)
    if a.pg:
        http_retry()
    bad = [x for x in RESULTS if not x["ok"]]
    print(f"env checks: {len(RESULTS) - len(bad)} of {len(RESULTS)} as the models say")
    if a.json:
        json.dump(RESULTS, open(a.json, "w"), indent=1)


if __name__ == "__main__":
    main()
