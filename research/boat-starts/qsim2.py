"""A shared work queue for the boat pool, against the per-batch policy ("new", cap 50), on today's mix replayed v times
a day (a design study: nothing here is in modal/boat.py).

The queue: every batch's jobs go into one queue; worker VMs (2 slots of 2 vCPU and 4 GB; a whole-VM job takes both,
a large job its own large worker) pull from it. Hard rules: a worker is up only while it runs a job or is about to
take one from a non-empty queue; it stops after 60 s with nothing to take; no placeholder work, no keep-alive; every
start within boat's limits and the reserve (60 a day, 15 an hour).

Levers (a policy's parameters):
- order: "rr" (round-robin across batches, longest first within each), "fifo" (the oldest batch's longest first),
  "lpt" (the longest queued job of any batch);
- H: a worker is started only when the queued urgent work beyond what the workers there take within SOON seconds
  would give each new worker at least H seconds of work, and the pool stays under `max` workers;
- priorities: urgent work (today's batches) first; background work (bg: a backlog of benchmark runs whose results
  are used, submitted at each day's start) only on slots no urgent job wants, starting workers of its own only
  within `bg_max` workers (0: none of its own: it fills the urgent pool's spare slots);
- submissions: "observed" (each batch when it came today), "serial" (a track's next batch THINK seconds after its
  last one ended), "pipelined" (up to 2 of a track's batches in flight).

    python3 research/boat-starts/qsim2.py research/boat-starts/mix.json > research/boat-starts/queue2-500.txt
"""
import argparse
import bisect
import heapq
import itertools
import math
import random
import sys
from collections import deque

sys.path.insert(0, __import__("os").path.dirname(__file__))
import sim

DAY = 86400.0
SOON = sim.BOOT + 20.0
MODAL_CHC_WALL = 330.1  # runs/modal/arith/chc-gdp: the user's line is about 3 times it


class W:
    __slots__ = ("id", "type", "slots", "free", "up_t", "ready", "prepped", "gen", "stopped", "running", "bg")

    def __init__(self, i, t, now, bg=False):
        self.id, self.type, self.bg = i, t, bg
        self.slots = 4 if t == "large" else 2
        self.free, self.up_t, self.ready = self.slots, now, False
        self.prepped, self.gen, self.stopped, self.running = set(), 0, False, []


class QB:
    def __init__(self, b, t0, bg=False):
        self.b, self.t0, self.bg = b, t0, bg
        kind = b["kind"] or "runner"
        self.prep = sim.PREP[kind]
        self.q = {}
        for j in b["jobs"]:
            self.q.setdefault((j[2], j[1]), []).append(j[0] + sim.OVERHEAD[kind])
        for k in self.q:
            self.q[k].sort()
        self.qwork = {"default": 0.0, "large": 0.0}  # slot-seconds queued
        self.qslots = {"default": 0, "large": 0}
        for (t, w), xs in self.q.items():
            self.qwork[t] += sum(xs) * w
            self.qslots[t] += len(xs) * w
        self.left = len(b["jobs"])
        self.started = 0
        self.end, self.modal = None, False
        self.done_work = 0.0

    def head(self, t, free):
        best = None
        for (tt, w), xs in self.q.items():
            if tt == t and w <= free and xs and (best is None or xs[-1] > best[0]):
                best = (xs[-1], w)
        return best

    def pop(self, t, j):
        self.q[(t, j[1])].pop()
        self.qwork[t] -= j[0] * j[1]
        self.qslots[t] -= j[1]


class QSim:
    def __init__(self, pol, plan="500"):
        self.p = pol
        self.lim_min, self.lim_hour, self.lim_day, self.lim_active = sim.PLANS[plan]
        self.reserve = (60, 15)
        self.ev, self.seq = [], itertools.count()
        self.starts, self.workers, self.live = [], [], []
        self.urgent, self.bgq = deque(), deque()
        self.batches = []
        self.now = 0.0
        self.days = {}
        self.on_end = None

    def at(self, t, f, *a):
        heapq.heappush(self.ev, (t, next(self.seq), f, a))

    def run(self, until):
        while self.ev and self.ev[0][0] <= until:
            t, _, f, a = heapq.heappop(self.ev)
            self.now = t
            f(*a)
        self.now = until
        for w in list(self.live):
            self.stop(w)
        return self

    def count(self, span):
        return len(self.starts) - bisect.bisect_right(self.starts, self.now - span)

    def left(self):
        rd, rh = self.reserve
        return max(0, min(self.lim_hour - self.count(3600) - rh, self.lim_day - self.count(86400) - rd))

    def room_now(self):
        return max(0, min(self.lim_min - self.count(60), self.left(), self.lim_active - len(self.live)))

    def book(self, kind, t0, t1, slots):
        while t1 > t0:
            k = int(t0 // DAY)
            e = min(t1, (k + 1) * DAY)
            d = self.days.setdefault(k, {"held": 0.0, "busy": 0.0, "dollars": 0.0, "bg_done": 0.0})
            d[kind] += (e - t0) * slots
            t0 = e

    # submissions
    def arrive(self, b, bg=False):
        B = QB(b, self.now, bg)
        self.batches.append(B)
        if not b["jobs"]:
            B.end = self.now
            self.ended(B)
            return
        (self.bgq if bg else self.urgent).append(B)
        if not bg:
            self.at(self.now + sim.MAX_WAIT, self.check_wait, B)
        self.schedule()

    def ended(self, B):
        if self.on_end and not B.bg:
            self.on_end(B.b, self.now)

    def check_wait(self, B):
        if B.started == 0 and B.end is None and self.left() <= 0 and not any(w.free and w.ready for w in self.live):
            B.modal, B.end, B.left = True, self.now, 0
            B.q = {}
            B.qwork = {"default": 0.0, "large": 0.0}
            B.qslots = {"default": 0, "large": 0}
            if B in self.urgent:
                self.urgent.remove(B)
            self.ended(B)

    # the pool
    def start_worker(self, t, bg=False):
        w = W(len(self.workers), t, self.now, bg)
        self.workers.append(w)
        self.live.append(w)
        self.starts.append(self.now)
        self.at(self.now + sim.BOOT, self.ready, w)

    def ready(self, w):
        w.ready = True
        self.schedule()
        self.idle_check(w)

    def pick(self, w):
        """The next job for a worker's free slots: urgent first (in the policy's order), then background (oldest
        first)."""
        order = self.p.get("order", "rr")
        if self.urgent:
            if order == "lpt":
                best = None
                for B in self.urgent:
                    j = B.head(w.type, w.free)
                    if j and (best is None or j[0] > best[1][0]):
                        best = (B, j)
                if best:
                    return best
            elif order == "srpt":  # the batch with the least work left first (its longest job), aged so none starves
                best = None
                for B in self.urgent:
                    j = B.head(w.type, w.free)
                    if j:
                        key = B.qwork["default"] + B.qwork["large"] - self.p.get("age", 1.0) * 2 * (self.now - B.t0) * 50
                        if best is None or key < best[0]:
                            best = (key, B, j)
                if best:
                    return best[1], best[2]
            elif order == "fifo":
                for B in self.urgent:
                    j = B.head(w.type, w.free)
                    if j:
                        return B, j
            else:  # rr: the next batch in turn that has a job for this worker
                for _ in range(len(self.urgent)):
                    B = self.urgent[0]
                    self.urgent.rotate(-1)
                    j = B.head(w.type, w.free)
                    if j:
                        return B, j
        for B in self.bgq:
            j = B.head(w.type, w.free)
            if j:
                return B, j
        return None

    def schedule(self):
        for w in list(self.live):
            if not w.ready:
                continue
            while w.free > 0:
                got = self.pick(w)
                if not got:
                    break
                B, j = got
                B.pop(w.type, j)
                d = j[0] + (0 if B in w.prepped else B.prep)
                w.prepped.add(B)
                w.free -= j[1]
                w.gen += 1
                B.started += 1
                end = self.now + d
                w.running.append((end, B.bg))
                self.at(end, self.done, w, B, j, d, end)
        self.grow()

    def done(self, w, B, j, d, end):
        w.free += j[1]
        self.book("busy", self.now - d, self.now, j[1])
        if B.bg:
            self.book("bg_done", self.now - d, self.now, j[1])
        w.running.remove((end, B.bg))
        w.gen += 1
        B.left -= 1
        if B.left == 0:
            B.end = self.now
            q = self.bgq if B.bg else self.urgent
            if B in q:
                q.remove(B)
            self.ended(B)
        self.schedule()
        self.idle_check(w)

    def grow(self):
        # a large worker for each queued large job beyond the large workers there are
        ql = sum(B.qslots["large"] // 4 for B in itertools.chain(self.urgent, self.bgq))
        have = sum(1 for w in self.live if w.type == "large")
        while ql > have and self.room_now() > 0:
            self.start_worker("large")
            have += 1
        live = [w for w in self.live if w.type == "default"]
        # capacity within SOON: free slots, booting workers, slots whose job ends by then
        soon = sum(w.free if w.ready else 2 for w in live) + sum(1 for w in live for e, _ in w.running if e <= self.now + SOON)
        uq_slots = sum(B.qslots["default"] for B in self.urgent)
        uq_work = sum(B.qwork["default"] for B in self.urgent)
        H, mx = self.p.get("H", 0), self.p["max"]
        if self.p.get("D") and uq_slots > soon:
            # drain: enough workers that the urgent work outstanding (queued and running) ends within D seconds
            run = sum(max(0.0, e - self.now) for w in live for e, bg in w.running if not bg)
            target = min(mx, math.ceil((uq_work + run) / (2 * self.p["D"])))
            k = target - len(live)
            while k > 0 and self.room_now() > 0:
                self.start_worker("default")
                k -= 1
            return
        if uq_slots > soon:
            # the urgent work beyond what's taken soon, spread so that each new worker gets H seconds or more
            beyond = uq_work * (uq_slots - soon) / uq_slots
            k = min(math.floor(beyond / (2 * H)) if H else math.ceil((uq_slots - soon) / 2), mx - len(live))
            if k <= 0 and not live:
                k = 1  # (work queued and no worker: one, whatever H says)
            while k > 0 and self.room_now() > 0:
                self.start_worker("default")
                k -= 1
            return
        # background: workers of its own only within bg_max, each with H seconds of it or more
        bq_slots = sum(B.qslots["default"] for B in self.bgq)
        if bq_slots > soon and self.p.get("bg_max", 0):
            bq_work = sum(B.qwork["default"] for B in self.bgq)
            nbg = sum(1 for w in live if w.bg)
            k = min(math.floor(bq_work * (bq_slots - soon) / bq_slots / (2 * max(H, 1))), self.p["bg_max"] - nbg, mx - len(live))
            while k > 0 and self.room_now() > 0:
                self.start_worker("default", bg=True)
                k -= 1

    def idle_check(self, w):
        if w.ready and not w.stopped and w.free == w.slots:
            self.at(self.now + 60, self.maybe_stop, w, w.gen)

    def maybe_stop(self, w, gen):
        if w.gen == gen and not w.stopped and w.free == w.slots:
            self.stop(w)

    def stop(self, w):
        w.stopped = True
        self.live.remove(w)
        self.book("held", w.up_t, self.now, w.slots)
        d = (self.now - w.up_t) * sim.VM_DOLLARS_S * (2 if w.type == "large" else 1)
        k = int(w.up_t // DAY)
        self.days.setdefault(k, {"held": 0.0, "busy": 0.0, "dollars": 0.0, "bg_done": 0.0})["dollars"] += d


# ------------------------------------------------------------------------------------------------- submissions
def tracks(mix):
    """Today's batches by track (runs/<track>/...), each track's in the order they came."""
    out = {}
    for b in mix:
        out.setdefault(b["run"].split("/")[1], []).append(b)
    return {k: sorted(v, key=lambda b: b["start"]) for k, v in out.items()}


class Driver:
    """Submits each replay's tracks' batches: when they came (observed), or each after the track's last result and a
    think time (serial), or with up to two in flight (pipelined)."""

    def __init__(self, S, mix, v, mode, seed=1, days=3):
        self.S, self.mode, self.rng = S, mode, random.Random(seed)
        t0 = min(b["start"] for b in mix)
        self.seqs = []
        k = 0
        while k * DAY / v < days * DAY:
            for name, bs in tracks(mix).items():
                off = k * DAY / v - t0
                seq = [dict(b, start=b["start"] + off, run=f"{b['run']}#{k}") for b in bs]
                self.seqs.append(seq)
            k += 1
        self.next = {}  # run -> (sequence, index)
        S.on_end = self.end
        for seq in self.seqs:
            if mode == "observed":
                for b in seq:
                    S.at(b["start"], self.submit, b)
            else:
                self.inflight = getattr(self, "inflight", {})
                self.inflight[id(seq)] = 0
                self.pos = getattr(self, "pos", {})
                self.pos[id(seq)] = 0
                for b in seq:
                    self.next[b["run"]] = seq
                S.at(seq[0]["start"], self.launch, seq)

    def think(self):
        return self.rng.uniform(300, 1200)

    def submit(self, b):
        self.S.arrive(b) if isinstance(self.S, QSim) else self.S.arrive(b)

    def launch(self, seq):
        i = self.pos[id(seq)]
        if i >= len(seq):
            return
        self.pos[id(seq)] = i + 1
        self.inflight[id(seq)] += 1
        self.submit(dict(seq[i], start=self.S.now))
        if self.mode == "pipelined" and self.inflight[id(seq)] < 2 and i + 1 < len(seq):
            self.S.at(self.S.now + 60, self.launch, seq)  # the next one submitted a minute later, before the result

    def end(self, b, t):
        if self.mode == "observed":
            return
        seq = self.next.get(b["run"])
        if seq is None:
            return
        self.inflight[id(seq)] -= 1
        if self.inflight[id(seq)] < (2 if self.mode == "pipelined" else 1):
            self.S.at(t + self.think(), self.launch, seq)


def background(S, per_day, days=3, mix=None):
    """per_day benchmark runs a day (CHC, TIP and termination in turn, today's measured jobs), submitted at each day's
    start as background work."""
    bench = [b for b in mix if b["run"] in ("runs/backends/chc-gdp", "runs/backends/tip-gdp3", "runs/backends/term-gdp")]
    k = 0
    for d in range(days):
        for i in range(per_day):
            b = bench[k % len(bench)]
            k += 1
            S.at(d * DAY + i * DAY / max(per_day, 1), S.arrive, dict(b, run=f"bg/{b['run']}#{d}.{i}"), True)
    return sum(sum(j[0] * j[1] for j in bench[i % len(bench)]["jobs"]) for i in range(per_day))


# ------------------------------------------------------------------------------------------------- the figures
def stats(rows, starts, held, busy, dollars, bg=None):
    r = [x for x in rows if 2 * DAY <= x["t0"] < 3 * DAY and not x.get("bg")]
    bench = sorted(x["wall"] for x in r if x["jobs"] >= 500 and not x["modal"])
    suites = sorted(x["wall"] for x in r if 168 <= x["jobs"] <= 204 and not x["modal"])
    med = lambda xs: round(xs[len(xs) // 2]) if xs else None
    s3 = sum(1 for t in starts if 2 * DAY <= t < 3 * DAY)
    over = sum(1 for x in bench if x > 3 * MODAL_CHC_WALL)
    out = {"starts": s3, "slot_h_per_start": round(busy / 3600 / max(s3, 1), 2), "util": round(busy / held, 3) if held else None,
           "modal": sum(x["modal"] for x in r), "modal_dollars": round(sum(x["modal_dollars"] for x in r), 2), "boat": round(dollars, 2),
           "suite": (med(suites), round(suites[-1]) if suites else None), "bench": (med(bench), round(bench[-1]) if bench else None),
           "bench_over_3x_modal": f"{over}/{len(bench)}", "batches": len(r)}
    if bg is not None:
        out["bg_done_of"] = bg
    return out


def run_new(mix, v, mode, plan, bg_per_day=0):
    S = sim.Sim([], sim.POLICIES["new"], plan)
    Driver(S, mix, v, mode)
    if bg_per_day:  # the per-batch policy has no priorities: the backlog runs as ordinary batches
        bench = [b for b in mix if b["run"] in ("runs/backends/chc-gdp", "runs/backends/tip-gdp3", "runs/backends/term-gdp")]
        k = 0
        for d in range(3):
            for i in range(bg_per_day):
                b = bench[k % len(bench)]
                k += 1
                S.at(d * DAY + i * DAY / bg_per_day, S.arrive, dict(b, run=f"bg/{b['run']}#{d}.{i}"))
    S.run()
    r = S.report()
    rows = [dict(x, bg=x["run"].startswith("bg/")) for x in r["rows"]]
    d = S.days.get(2, {"held": 0.0, "busy": 0.0, "tail": 0.0})
    held, busy = (d["held"] + d["tail"]) * 2, d["busy"] * 2
    bgrows = [x for x in rows if x["bg"] and 2 * DAY <= x["t0"] < 3 * DAY]
    bg = f"{sum(1 for x in bgrows if x['done'] and not x['modal'] and x['t0'] + x['wall'] < 3 * DAY)}/{len(bgrows)} runs" if bg_per_day else None
    return stats(rows, S.starts, held, busy, S.day_dollars(2)[0], bg)


def run_queue(mix, v, mode, plan, pol, bg_per_day=0):
    Q = QSim(pol, plan)
    Driver(Q, mix, v, mode)
    if bg_per_day:
        background(Q, bg_per_day, mix=mix)
    Q.run(3 * DAY + 6 * 3600)
    rows = []
    for B in Q.batches:
        b = B.b
        rows.append({"run": b["run"], "t0": B.t0, "wall": (B.end if B.end is not None else Q.now) - B.t0, "modal": B.modal, "jobs": len(b["jobs"]), "bg": B.bg,
                     "modal_dollars": sum(j[0] for j in b["jobs"]) * sim.modal_rate(b) if B.modal else 0.0, "done": B.end is not None})
    d = Q.days.get(2, {"held": 0.0, "busy": 0.0, "dollars": 0.0, "bg_done": 0.0})
    bgb = [B for B in Q.batches if B.bg and 2 * DAY <= B.t0 < 3 * DAY]
    bg = f"{sum(1 for B in bgb if B.end is not None and B.end < 3 * DAY)}/{len(bgb)} runs" if bg_per_day else None
    return stats(rows, Q.starts, d["held"], d["busy"], d["dollars"], bg)


POLS = {
    "queue rr drain D=300 max=100": {"order": "rr", "D": 300, "max": 100},
    "queue rr drain D=450 max=100": {"order": "rr", "D": 450, "max": 100},
    "queue rr drain D=600 max=100": {"order": "rr", "D": 600, "max": 100},
    "queue rr drain D=900 max=100": {"order": "rr", "D": 900, "max": 100},
    "queue fifo drain D=450 max=100": {"order": "fifo", "D": 450, "max": 100},
    "queue srpt drain D=300 max=100": {"order": "srpt", "D": 300, "max": 100},
    "queue srpt drain D=450 max=100": {"order": "srpt", "D": 450, "max": 100},
    "queue srpt drain D=900 max=100": {"order": "srpt", "D": 900, "max": 100},
    "queue srpt drain D=600 max=100": {"order": "srpt", "D": 600, "max": 100},
    "queue srpt drain D=600 max=150": {"order": "srpt", "D": 600, "max": 150},
    "queue lpt drain D=450 max=100": {"order": "lpt", "D": 450, "max": 100},
    "queue rr H=0 max=50": {"order": "rr", "H": 0, "max": 50},
    "queue rr H=300 max=100": {"order": "rr", "H": 300, "max": 100},
    "queue rr H=600 max=100": {"order": "rr", "H": 600, "max": 100},
    "queue rr H=900 max=100": {"order": "rr", "H": 900, "max": 100},
    "queue rr H=600 max=50": {"order": "rr", "H": 600, "max": 50},
    "queue rr H=600 max=200": {"order": "rr", "H": 600, "max": 200},
    "queue fifo H=600 max=100": {"order": "fifo", "H": 600, "max": 100},
    "queue lpt H=600 max=100": {"order": "lpt", "H": 600, "max": 100},
}

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("mix")
    ap.add_argument("--plan", default="500")
    ap.add_argument("--v", default="1,2,3,4,5")
    ap.add_argument("--modes", default="observed,serial,pipelined")
    ap.add_argument("--bg", default="0,2")
    ap.add_argument("--pols", default="queue rr drain D=600 max=100,queue srpt drain D=300 max=100,queue srpt drain D=450 max=100,queue srpt drain D=600 max=100,queue srpt drain D=600 max=150,queue srpt drain D=900 max=100")
    a = ap.parse_args()
    mix = sim.load(a.mix)
    print(f"plan ${a.plan} {sim.PLANS[a.plan][:3]}, reserve 60 a day and 15 an hour; day 3 of each replay; walls (s) from submission to the last job; "
          f"bench over 3x: benchmark runs slower than {round(3 * MODAL_CHC_WALL, 1)} s")
    print("v    submit     bg/day  policy                      starts  slot-h/start  util   Modal (batches, $)  boat $  suite med/max  bench med/max  bench>3x  background done")
    for v in [float(x) for x in a.v.split(",")]:
        for mode in a.modes.split(","):
            for bgd in [int(x) for x in a.bg.split(",")]:
                rows = [("new (per batch, cap 50)", run_new(mix, v, mode, a.plan, bgd))]
                for name in a.pols.split(","):
                    rows.append((name, run_queue(mix, v, mode, a.plan, POLS[name], bgd)))
                for name, s in rows:
                    print(f"{v:<4} {mode:10} {bgd:6}  {name:26} {s['starts']:6}  {s['slot_h_per_start']:12}  {s['util']:5}  {s['modal']:4} (${s['modal_dollars']:7})  {s['boat']:6}"
                          f"  {str(s['suite']):13}  {str(s['bench']):13}  {s['bench_over_3x_modal']:8}  {s.get('bg_done_of') or '-'}", flush=True)
