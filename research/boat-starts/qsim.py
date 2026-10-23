"""A global work queue instead of per-batch leases (a design, not the code): every batch from every track puts its
jobs in one queue (longest first within a batch, round-robin across batches), and a pool of worker VMs pulls from it.

- Bring-up: a worker is started only when the queue holds more slot-work than the running workers can take within
  SOON seconds (free slots, slots whose job ends by then, workers still booting), and only within the pool's target
  (`target` workers, or `adaptive`: enough that the work outstanding drains in `H` seconds), the starts left and the
  reserve (sim.py's limits: rolling minute, hour and day).
- Shutdown: a worker stops after `idle` (60) seconds with nothing to take; it is never kept up to save a start.
- A worker pays PREP the first time it runs a job of a batch (the batch's fresh tree), BOOT + PREP when started.
- A job needing a whole VM takes both slots of one; a job needing a large VM starts (or reuses) a large worker.
- A batch none of whose jobs has started --max-wait (120 s) after it came, with no start left, goes to Modal.

    python3 research/boat-starts/qsim.py research/boat-starts/mix.json [--plan 500] [--v 1,2,3,4,5] > research/boat-starts/queue-500.txt
"""
import argparse
import bisect
import heapq
import itertools
import math
import sys

sys.path.insert(0, __import__("os").path.dirname(__file__))
import sim

SOON = sim.BOOT + 20.0  # a job that would wait longer than a new worker takes to be ready wants one


class W:
    __slots__ = ("id", "type", "slots", "free", "up_t", "busy", "ready", "prepped", "gen", "stopped", "running")

    def __init__(self, i, t, now):
        self.id, self.type = i, t
        self.slots = 4 if t == "large" else 2
        self.free, self.up_t, self.busy, self.ready = self.slots, now, 0.0, False
        self.prepped, self.gen, self.stopped, self.running = set(), 0, False, []


class QB:
    def __init__(self, b, t0):
        self.b, self.t0 = b, t0
        kind = b["kind"] or "runner"
        self.prep = sim.PREP[kind]
        self.q = {}  # (type, weight) -> durations, longest last
        for j in b["jobs"]:
            self.q.setdefault((j[2], j[1]), []).append(j[0] + sim.OVERHEAD[kind])
        for k in self.q:
            self.q[k].sort()
        self.left = len(b["jobs"])
        self.started = 0
        self.end = None
        self.modal = False
        self.modal_part = 0

    def queued(self, t):
        return sum(len(xs) * w for (tt, w), xs in self.q.items() if tt == t)

    def take(self, t, free):
        best = None
        for (tt, w), xs in self.q.items():
            if tt == t and w <= free and xs and (best is None or xs[-1] > best[0]):
                best = (xs[-1], w)
        if best:
            self.q[(t, best[1])].pop()
        return best


class QSim:
    def __init__(self, mix, pol, plan="500"):
        self.mix, self.p = mix, pol
        self.lim_min, self.lim_hour, self.lim_day, self.lim_active = sim.PLANS[plan]
        self.reserve = pol.get("reserve", (60, 15))
        self.ev, self.seq = [], itertools.count()
        from collections import deque
        self.starts, self.workers, self.batches, self.rr, self.live = [], [], [], deque(), []
        self.now = 0.0
        self.days = {}
        self.booting = 0

    def at(self, t, f, *a):
        heapq.heappush(self.ev, (t, next(self.seq), f, a))

    def run(self):
        for b in self.mix:
            self.at(b["start"], self.arrive, b)
        while self.ev:
            t, _, f, a = heapq.heappop(self.ev)
            self.now = t
            f(*a)
        return self

    # limits, as sim.Sim
    def count(self, span):
        return len(self.starts) - bisect.bisect_right(self.starts, self.now - span)

    def left(self):
        rd, rh = self.reserve
        return max(0, min(self.lim_hour - self.count(3600) - rh, self.lim_day - self.count(86400) - rd))

    def room_now(self):
        up = len(self.live)
        return max(0, min(self.lim_min - self.count(60), self.left(), self.lim_active - up))

    def book(self, kind, t0, t1, w, frac=1.0):
        m = (2 if w.type == "large" else 1) * frac
        while t1 > t0:
            k = int(t0 // 86400)
            e = min(t1, (k + 1) * 86400)
            d = self.days.setdefault(k, {"up": 0.0, "busy": 0.0})
            d[kind] += (e - t0) * m
            t0 = e

    # batches
    def arrive(self, b):
        B = QB(b, self.now)
        self.batches.append(B)
        if not b["jobs"]:
            B.end = self.now
            return
        self.rr.append(B)
        self.at(self.now + sim.MAX_WAIT, self.check_wait, B)
        self.schedule()

    def check_wait(self, B):
        if B.started == 0 and B.end is None and self.left() <= 0 and not any(w.free and w.ready for w in self.live):
            B.modal, B.end, B.left = True, self.now, 0
            B.q = {}
            if B in self.rr:
                self.rr.remove(B)

    # the pool
    def start_worker(self, t):
        w = W(len(self.workers), t, self.now)
        self.workers.append(w)
        self.live.append(w)
        self.starts.append(self.now)
        self.booting += 1
        self.at(self.now + sim.BOOT, self.ready, w)
        return w

    def ready(self, w):
        w.ready = True
        self.booting -= 1
        self.schedule()
        self.idle_check(w)

    def schedule(self):
        """Fills free slots round-robin across batches, then starts workers the queue needs."""
        for t in ("default", "large"):
            for w in list(self.live):
                if w.type != t or not w.ready:
                    continue
                while w.free > 0 and self.assign(w):
                    pass
        self.grow()

    def assign(self, w):
        n = len(self.rr)
        for k in range(n):
            B = self.rr[0]
            self.rr.rotate(-1)
            j = B.take(w.type, w.free)
            if j is None:
                continue
            d = j[0] + (0 if B in w.prepped else B.prep)
            w.prepped.add(B)
            w.free -= j[1]
            w.gen += 1
            B.started += 1
            end = self.now + d
            w.running.append(end)
            self.at(end, self.done, w, B, j, d, end)
            return True
        return False

    def done(self, w, B, j, d, end):
        w.free += j[1]
        w.busy += d * j[1] / w.slots
        self.book("busy", self.now - d, self.now, w, j[1] / w.slots)
        w.running.remove(end)
        w.gen += 1
        B.left -= 1
        if B.left == 0:
            B.end = self.now
            if B in self.rr:
                self.rr.remove(B)
        self.schedule()
        self.idle_check(w)

    def grow(self):
        # large jobs: a large worker for each queued one beyond the large workers there are
        qlarge = sum(1 for B in self.rr for (t, w), xs in B.q.items() if t == "large" for _ in xs)
        have = sum(1 for w in self.live if w.type == "large")
        while qlarge > have and self.room_now() > 0:
            self.start_worker("large")
            have += 1
        # default: the slot-work queued beyond what the workers there are take within SOON
        queued = sum(B.queued("default") for B in self.rr)
        if queued <= 0:
            return
        live = [w for w in self.live if w.type == "default"]
        soon = sum(w.free for w in live if w.ready) + 2 * sum(1 for w in live if not w.ready)
        soon += sum(1 for w in live for e in w.running if e <= self.now + SOON)
        need = math.ceil(max(0, queued - soon) / 2)
        if need <= 0:
            return
        if self.p.get("adaptive"):
            work = sum(x * w for B in self.rr for (t, w), xs in B.q.items() if t == "default" for x in xs)
            target = math.ceil(work / (2 * self.p["H"]))
        else:
            target = self.p["target"]
        k = min(need, target - len(live))
        while k > 0 and self.room_now() > 0:
            self.start_worker("default")
            k -= 1

    def idle_check(self, w):
        if w.ready and not w.stopped and w.free == w.slots:
            self.at(self.now + self.p.get("idle", 60), self.maybe_stop, w, w.gen)

    def maybe_stop(self, w, gen):
        if w.gen == gen and not w.stopped and w.free == w.slots:
            w.stopped = True
            self.live.remove(w)
            self.book("up", w.up_t, self.now, w)

    def finish(self):
        for w in list(self.live):
            w.stopped = True
            self.book("up", w.up_t, self.now, w)
        self.live = []

    def day(self, k):
        d = self.days.get(k, {"up": 0.0, "busy": 0.0})
        return round(d["up"] * sim.VM_DOLLARS_S, 3), round((d["up"] - d["busy"]) * sim.VM_DOLLARS_S, 3)

    def rows(self):
        out = []
        for B in self.batches:
            b = B.b
            out.append({"run": b["run"], "t0": B.t0, "wall": round((B.end if B.end is not None else self.now) - B.t0, 1), "modal": B.modal,
                        "jobs": len(b["jobs"]), "modal_dollars": round(sum(j[0] for j in b["jobs"]) * sim.modal_rate(b), 4) if B.modal else 0.0,
                        "done": B.end is not None})
        return out


def third_day_stats(rows, starts, dollars):
    DAY = 86400.0
    r = [x for x in rows if 2 * DAY <= x["t0"] < 3 * DAY]
    bench = sorted(x["wall"] for x in r if x["jobs"] >= 500 and not x["modal"])
    suites = sorted(x["wall"] for x in r if 168 <= x["jobs"] <= 204 and not x["modal"])
    med = lambda xs: xs[len(xs) // 2] if xs else None
    s3 = sum(1 for t in starts if 2 * DAY <= t < 3 * DAY)
    return (f"{s3:6} {sum(x['modal'] for x in r):4} {sum(x['jobs'] for x in r if x['modal']):6} {round(sum(x['modal_dollars'] for x in r), 2):7}"
            f"  {dollars[0]:6} ({dollars[1]:5})  suite {med(suites)} / {suites[-1] if suites else None}  bench {med(bench)} / {bench[-1] if bench else None}"
            f"  unfinished {sum(not x['done'] for x in r)}")


if __name__ == "__main__":
    from collections import deque
    ap = argparse.ArgumentParser()
    ap.add_argument("mix")
    ap.add_argument("--plan", default="500")
    ap.add_argument("--v", default="1,2,3,4,5")
    a = ap.parse_args()
    from scale import replay
    pols = [("queue 25", {"target": 25}), ("queue 50", {"target": 50}), ("queue 100", {"target": 100}),
            ("queue adaptive H=600", {"adaptive": True, "H": 600}), ("queue adaptive H=300", {"adaptive": True, "H": 300})]
    print(f"plan ${a.plan} {sim.PLANS[a.plan][:3]}, reserve 60 a day and 15 an hour; day 3 of each replay")
    print("v    policy                  starts  to Modal: batches jobs $   boat $ (idle $)  suite wall median / slowest  benchmark wall median / slowest")
    for v in [float(x) for x in a.v.split(",")]:
        m = replay(v)
        S = sim.Sim(m, sim.POLICIES["new"], a.plan).run()
        r = S.report()
        print(f"{v:<4} {'new (per batch, cap 50)':24}" + third_day_stats(r["rows"], S.starts, S.day_dollars(2)))
        for name, p in pols:
            Q = QSim(m, dict(p, idle=60), a.plan)
            Q.run()
            Q.finish()
            print(f"{v:<4} {name:24}" + third_day_stats(Q.rows(), Q.starts, Q.day(2)))
