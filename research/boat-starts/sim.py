"""A day of batches on the boat pool under a scheduling policy: the starts it spends, what falls back to Modal, each
batch's wall time and the dollars (boat's VM-seconds, the idle ones apart, and Modal's for what fell back).

    python3 research/boat-starts/sim.py research/boat-starts/mix.json [--policy NAME ...] [--plan 100|500] [--rows]

The mix (mix.py) is today's batches as they arrived, each with its jobs' measured seconds and weights. The model:

- boat's limits are rolling windows (the $100 plan: 30 starts a minute, 210 an hour, 840 a day; 300 VMs up); a
  creation and a resume are one start each, a VM still up (released less than its idle time ago) is leased without
  one. As modal/boat.py, 10 starts of the hour and of the day are never spent.
- A started VM is ready BOOT + PREP seconds after its start, PREP after its lease when it was up: the typical
  `to_running_s` and `prep_s` of the runs' backends.json (run.py's batches prepare the Lean library too). Starts go
  round-robin to the batches that want them, within the minute's room. A batch stops creating VMs once its VMs have
  slots for all it has left (Session.enough()); the old code resumes every stopped VM it leased regardless, the new
  one checks before each resume too.
- A VM takes the longest queued job that fits its free slots (2 a default VM, 4 a large one; a TIP call takes 2),
  each job its measured seconds plus OVERHEAD (a compare runner's call: the solver's seconds are in results.jsonl,
  the call's process and import around them are not).
- A batch that can get no VM falls back to Modal (old: at once; new: once it has waited `wait` seconds for a VM
  another batch releases). Modal's dollars are its measured dollars per job-second (the README's Backends table).
- When a batch's last job ends it releases its VMs; each stays up `idle` seconds (with a floor: the first `floor`
  released while fewer than that are kept long stay `floor_T`), then stops. With `topup`, a batch that has more work
  than slots leases each VM another batch releases, without a start.

Lane P (10-31, the $500 plan, week.json.gz from launches.py, `--since 2026-10-28T00:00:00Z --other 30` prints its
table, week-500.txt): `vm` large or xlarge VMs (TYPES: their slots and price); `other` the account's other project's
starts (bursts, counted against the plan, not us); `ceil` our share of the plan's day and hour and our starts a minute,
`dyn` the reserve at least twice the other's last day and hour; `tiny` a small batch on a VM already up, else Modal;
`demand` a released VM kept up to `long` s while its client declared work (a bar until its last launch starts, a lane
for `hb` s after each batch) and that client keeps fewer than it held at its peak in the last `window` s; `fleet` k
VMs kept up until `quiet` s pass with no batch arriving (the core fleet).

Batches arrive when they did today, whatever the policy (a track that waited longer for a result would have sent
its next batch later: the sim doesn't move them).
"""
import argparse
import bisect
import heapq
import itertools
import json
import math
import statistics
import sys

BOOT = 10.0
PREP = {"run.py": 22.0, "runner": 10.0}
OVERHEAD = {"run.py": 0.0, "runner": 5.0}  # calibrate.py: the least error against the old runs' progress lines
VM_DOLLARS_S = 1e-5  # a default VM (4 vCPU): $0.036 an hour; a large one (8 vCPU) twice that
# slots (2 vCPU and 4 GB each) and price against a default VM, by type (`boat limits`, 10-31: xlarge $0.20 an hour)
TYPES = {"default": (2, 1.0), "large": (4, 2.0), "xlarge": (8, 0.20 / 0.036)}
RESERVE = (10, 10)  # (day, hour) never spent: the code before; the policy's "reserve" overrides (boat.py: 60, 15)
MAX_WAIT = 120  # --max-wait's default
RETRY = 60  # a batch short of VMs asks for starts again this often (Session.run's top-up)
PLANS = {"100": (30, 210, 840, 300), "500": (65, 420, 1680, 1000), "2000": (90, 600, 2400, 2000), "inf": (10**6, 10**7, 10**8, 10**6), "minute": (30, 10**7, 10**8, 300)}
# $ per job-second on Modal: each the README's run (modal billing report) over its job seconds
MODAL_RATE = {"chc": 2.604 / 65830.4, "tip": 0.633 / 14016.7, "term": 2.122 / 50466.6, "run.py": 0.256 / 4246.7}


def modal_rate(b):
    name = b["run"].split("/")[-1]
    for k in ("chc", "tip", "term"):
        if k in name and b["kind"] == "runner":
            return MODAL_RATE[k]
    return MODAL_RATE["run.py"] if b["kind"] == "run.py" else MODAL_RATE["term"]


class VMx:
    __slots__ = ("id", "type", "slots", "free", "batch", "up", "stop_at", "busy", "held_s", "tail_s", "free_t", "lease_t", "gen", "ever", "owner", "fleet")

    def __init__(self, i, t):
        self.id, self.type = i, t
        self.slots = TYPES[t][0]
        self.free, self.batch, self.up, self.stop_at = self.slots, None, False, None
        self.busy = self.held_s = self.tail_s = 0.0
        self.free_t = self.lease_t = None
        self.gen, self.ever, self.owner, self.fleet = 0, False, None, False


class Batch:
    def __init__(self, b, t0, overhead, prep, jobs=None):
        self.b, self.t0, self.prep = b, t0, prep
        self.q = {}  # (type, weight) -> durations, longest last (popped from the end)
        for j in jobs or b["jobs"]:
            self.q.setdefault((j[2], j[1]), []).append(j[0] + overhead)
        for k in self.q:
            self.q[k].sort()
        self.qn = {}  # type -> jobs queued
        for (t, w), xs in self.q.items():
            self.qn[t] = self.qn.get(t, 0) + len(xs)
        self.slots = {}  # type -> slots of the VMs it holds
        self.vms, self.left, self.want = [], len(b["jobs"]), {}
        self.starts = self.warm = 0
        self.tiny = False
        self.fleet_n = 0  # of the VMs it starts, this many join the fleet
        self.end, self.modal, self.waited, self.done_t = None, False, 0.0, []
        self.modal_jobs, self.modal_seconds = 0, 0.0  # jobs of it that went to Modal while the rest ran on boat

    def take(self, vtype, free):
        """The longest queued job of this type whose weight fits `free` slots: (seconds, weight), or None."""
        best = None
        for (t, w), xs in self.q.items():
            if t == vtype and w <= free and xs and (best is None or xs[-1] > best[0]):
                best = (xs[-1], w)
        if best:
            self.q[(vtype, best[1])].pop()
            self.qn[vtype] -= 1
        return best

    def enough(self, t):
        return self.qn.get(t, 0) <= self.slots.get(t, 0)


class Sim:
    def __init__(self, mix, pol, plan="100", stopped=0, other=0, seed=1):
        self.mix, self.p = mix, pol
        self.main = pol.get("vm", "default")  # the type a batch's ordinary jobs run on
        self.mslots = TYPES[self.main][0]
        # the account's other project: `other` starts a day, in bursts of 1 to 8 a few minutes apart (its pool's
        # setup), over the mix's span; they count against the plan's limits, not ours
        self.others: list[float] = []
        if other and mix:
            import random
            rnd, t, t1 = random.Random(seed), min(b["start"] for b in mix) - 86400, max(b["start"] for b in mix) + 86400
            while True:
                t += rnd.expovariate(other / 4.5 / 86400)
                if t > t1:
                    break
                self.others += [t + 30 * k for k in range(rnd.randint(1, 8))]
            self.others.sort()
        self.held = {}  # track -> VMs its batches hold now; peaks: track -> [(t, held)] (the warm set's size)
        self.peaks = {}
        self.last_start = {}  # track -> its last batch's start (a bar knows its queue: demand until it empties)
        for b in mix:
            tr = b.get("track", b["run"])
            self.last_start[tr] = max(self.last_start.get(tr, 0), b["start"])
        self.lim_min, self.lim_hour, self.lim_day, self.lim_active = PLANS[plan]
        self.ev, self.seq = [], itertools.count()
        self.starts: list[float] = []  # in time order
        self.vms: list[VMx] = []
        self.stopped = {}  # type -> stopped VMs (resumable)
        self.upfree = {}  # type -> {id: VM} up and free
        self.active = 0
        self.batches, self.running = [], []
        self.now = 0.0
        self.pending = []  # batches that want starts
        self.waiting = []  # batches with no VM, waiting for one another batch releases
        self.dispatch_at = None
        self.days = {}
        for i in range(stopped):  # a pool of stopped VMs to resume (calibration)
            v = VMx(i, "default")
            v.ever = True
            self.vms.append(v)
            self.stopped.setdefault("default", []).append(v)

    def book(self, kind, t0, t1, v, frac=1.0):
        """VM-seconds of a kind (held by a batch, busy, up after release) by day (day k: [k, k+1) days from 0)."""
        m = TYPES[v.type][1] * frac
        while t1 > t0:
            k = int(t0 // 86400)
            e = min(t1, (k + 1) * 86400)
            d = self.days.setdefault(k, {"held": 0.0, "busy": 0.0, "tail": 0.0})
            d[kind] += (e - t0) * m
            t0 = e

    def day_dollars(self, k):
        d = self.days.get(k, {"held": 0.0, "busy": 0.0, "tail": 0.0})
        return round((d["held"] + d["tail"]) * VM_DOLLARS_S, 3), round((d["held"] - d["busy"] + d["tail"]) * VM_DOLLARS_S, 3)

    def ended(self, B):
        """A batch is done (or on Modal): a submission driver (subs.py) may send the track's next one."""
        if getattr(self, "on_end", None):
            self.on_end(B.b, self.now)

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

    # ------------------------------------------------------------------ the plan's limits
    def count(self, span):
        return len(self.starts) - bisect.bisect_right(self.starts, self.now - span)

    def ocount(self, span):
        """The other project's starts in the last `span` s."""
        return bisect.bisect_right(self.others, self.now) - bisect.bisect_right(self.others, self.now - span)

    def left(self):
        """Starts left this hour and day after the reserve (what plan_vms and the gate read): the account's (ours and
        the other project's) against the plan, and ours against our ceiling (`ceil`: shares of the day and hour)."""
        rd, rh = self.p.get("reserve", RESERVE)
        if self.p.get("dyn"):  # the reserve: at least twice what the other project used in the last day (hour)
            rd, rh = max(rd, 2 * self.ocount(86400)), max(rh, 2 * self.ocount(3600))
        h, d = self.count(3600), self.count(86400)
        k = min(self.lim_hour - h - self.ocount(3600) - rh, self.lim_day - d - self.ocount(86400) - rd)
        if self.p.get("ceil"):
            c = self.p["ceil"]
            k = min(k, int(c[0] * self.lim_day) - d, int(c[1] * self.lim_hour) - h)
        return max(0, k)

    def minute_room(self):
        m = self.lim_min - self.count(60) - self.ocount(60)
        return min(m, self.p["ceil"][2] - self.count(60)) if self.p.get("ceil") else m

    def room_now(self):
        return max(0, min(self.minute_room(), self.left(), self.lim_active - self.active))

    def short_projected(self):
        """Will the starts run out before the work does? At the last hour's pace p (its starts), the day's starts
        left last fewer than H hours, or the hour's left are fewer than p (the pace would spend the hour)."""
        a = self.p["adaptive"]
        p = self.count(3600)
        rd, rh = self.p.get("reserve", RESERVE)
        day_left = self.lim_day - self.count(86400) - rd
        hour_left = self.lim_hour - p - rh
        if a.get("exhaust"):  # at this pace the starts left run out within the long idle time itself
            return p > 0 and min(day_left, hour_left) < p * a["long"] / 3600
        return p > 0 and (day_left < p * a["H"] or (a.get("hour") and hour_left < p))

    # ------------------------------------------------------------------ sizing
    def plan_old(self, items, up):
        """modal/boat.py's plan_vms before this change."""
        if not items:
            return 0
        W = sum(j[0] * j[1] for j in items)
        L = max(j[0] for j in items)
        useful = max(1, math.ceil(W / (self.mslots * max(L, 1e-9))))
        useful = min(useful, sum(j[1] for j in items) // self.mslots + 1, len(items))
        by_rate = up + math.ceil(math.sqrt(2 * (self.lim_min / 60) * W / self.mslots))
        room = self.lim_active - self.active + up
        return max(1, min(useful, by_rate, room, up + self.left()))

    def size(self, items, up):
        if self.p.get("force"):
            return self.p["force"]
        n = self.plan_old(items, up)
        if self.p.get("share") is not None:
            left = self.left()
            budget = min(left, max(self.p.get("min_budget", 2), math.floor(self.p["share"] * left)))
            cap = self.p.get("cap")
            if self.p.get("cap_short") and self.count(3600) * self.p["cap_short"][1] > left:
                cap = self.p["cap_short"][0]  # at the last hour's pace the starts left last under H hours: the lower cap
            if cap:
                budget = min(budget, cap)
            n = min(n, up + budget)
        elif self.p.get("cap"):
            n = min(n, self.p["cap"])
        return max(n, 0)

    # ------------------------------------------------------------------ a batch
    def vtype(self, w):
        """The type a job of weight w runs on: the batch's own, else the smallest that has the slots."""
        return next((t for t in (self.main, "large", "xlarge") if TYPES[t][0] >= w and TYPES[t][0] >= self.mslots), "xlarge")

    def arrive(self, b):
        kind = b["kind"] or "runner"
        jobs = [[j[0], j[1], self.vtype(j[1])] for j in b["jobs"]]
        B = Batch(b, self.now, OVERHEAD[kind], PREP[kind], jobs)
        self.batches.append(B)
        if not b["jobs"]:
            B.end = self.now
            self.ended(B)
            return
        self.running.append(B)
        types = {}
        for j in jobs:
            types.setdefault(j[2], []).append(j)
        tiny = self.p.get("tiny")  # a small batch: VMs already up only, else Modal; never a start
        tiny = tiny and (len(jobs) <= tiny[0] or sum(j[0] * j[1] for j in jobs) < tiny[1] * 60)
        for t, items in types.items():
            up = sorted(self.upfree.get(t, {}).values(), key=lambda v: v.free_t)
            n = self.size(items, len(up)) if t == self.main else len(items)  # (one large VM per job that needs it)
            k = min(n, len(up))
            for v in up[len(up) - k:]:
                self.lease(v, B, warm=True)
            B.want[t] = 0 if tiny else n - k
        if tiny:
            B.tiny = True
            if not B.vms:
                self.to_modal(B)
            else:
                self.strand(B)  # (its jobs of another type than the warm VMs': Modal)
            return
        if self.p.get("fleet"):
            self.wake_fleet(B)
        if not B.vms and self.left() <= 0:
            self.no_vm(B)
            return
        if any(B.want.values()):
            self.pending.append(B)
            self.dispatch()

    def no_vm(self, B):
        if self.p.get("wait") and any(C.vms and C.end is None for C in self.running):
            self.waiting.append(B)
            self.at(self.now + self.p["wait"], self.give_up, B)
            self.at(self.now + RETRY, self.retry, B)
        else:
            self.to_modal(B)

    def retry(self, B):
        """A batch that wanted VMs when no start was left, every RETRY s (Session.run's top-up): once starts are
        back and it still has more work than slots, its share of them (no more than it lacks)."""
        if B.end is not None or B.modal:
            return
        if B not in self.waiting and B.enough(self.main):
            return
        left = self.left()
        if left > 0 and B not in self.pending:
            lack = math.ceil((B.qn.get(self.main, 0) - B.slots.get(self.main, 0)) / self.mslots)
            budget = min(left, max(self.p.get("min_budget", 2), math.floor(self.p.get("share", 1) * left)))
            if B in self.waiting:
                self.waiting.remove(B)
            B.want[self.main] = max(0, min(lack, budget))
            self.pending.append(B)
            self.dispatch()
        self.at(self.now + RETRY, self.retry, B)

    def strand(self, B):
        """Jobs that need a VM type the batch got none of, once no more VMs come for it: on Modal (the run loop's
        "no boat large VM to be had", after --max-wait)."""
        if B.end is not None:
            return
        have = {v.type for v in B.vms if v.batch is B}
        for (t, w), xs in list(B.q.items()):
            if t not in have and xs:
                B.modal_jobs += len(xs)
                B.modal_seconds += sum(xs)
                B.qn[t] -= len(xs)
                B.left -= len(xs)
                B.q[(t, w)] = []
        if B.left == 0 and B.end is None:
            B.end = self.now
            self.ended(B)
            self.running.remove(B)
            for w in list(B.vms):
                if w.batch is B:
                    self.release(w)

    def give_up(self, B):
        if B in self.waiting:
            self.waiting.remove(B)
            self.to_modal(B)

    def to_modal(self, B):
        B.modal, B.end, B.left = True, self.now, 0
        self.ended(B)
        B.q, B.qn = {}, {}
        B.waited = self.now - B.t0
        if B in self.running:
            self.running.remove(B)

    def lease(self, v, B, warm):
        if warm:
            v.tail_s += self.now - v.free_t
            self.book("tail", v.free_t, self.now, v)
            self.upfree[v.type].pop(v.id, None)
            B.warm += 1
        else:
            B.starts += 1
            self.starts.append(self.now)
            v.fleet = B.fleet_n > 0 and v.type == self.main
            B.fleet_n -= v.fleet
            self.active += 1
        v.batch, v.gen, v.lease_t, v.up, v.free_t, v.ever, v.owner = B, v.gen + 1, self.now, True, None, True, None
        tr = B.b.get("track", B.b["run"])
        self.held[tr] = self.held.get(tr, 0) + 1
        self.peaks.setdefault(tr, []).append((self.now, self.held[tr]))
        B.vms.append(v)
        B.slots[v.type] = B.slots.get(v.type, 0) + v.slots
        self.at(self.now + B.prep + (0 if warm else BOOT), self.ready, v, v.gen)

    def dispatch(self):
        while self.pending:
            granted = False
            for B in list(self.pending):
                if B.end is not None:
                    self.pending.remove(B)
                    continue
                if self.left() <= 0:  # the hour or the day spent: no more VMs for anyone
                    for C in list(self.pending):
                        self.pending.remove(C)
                        if not C.vms:
                            self.no_vm(C)
                            continue
                        if any(k > 0 for t, k in C.want.items() if t != self.main):
                            self.at(max(self.now, C.t0 + MAX_WAIT), self.strand, C)
                        if C.want.get(self.main, 0) > 0 and self.p.get("topup"):  # short of VMs: asks again later
                            self.at(self.now + RETRY, self.retry, C)
                        C.want = {t: 0 for t in C.want}
                    return
                t = next((t for t, k in B.want.items() if k > 0), None)
                if t is None:
                    self.pending.remove(B)
                    continue
                stopped = self.stopped.get(t)
                # a creation checks whether the batch still needs it; a resume did only under the new policy
                if t == self.main and (not stopped or self.p.get("check_resume")) and B.enough(t):
                    B.want[t] = 0
                    continue
                if self.room_now() <= 0:
                    break
                if stopped:
                    v = stopped.pop()
                else:
                    v = VMx(len(self.vms), t)
                    self.vms.append(v)
                self.lease(v, B, warm=False)
                B.want[t] -= 1
                granted = True
            if not granted:
                break
        if self.pending and (self.dispatch_at is None or self.dispatch_at <= self.now):
            t = self.now + 1.0
            if self.minute_room() <= 0 and self.count(60):
                t = max(t, self.starts[bisect.bisect_right(self.starts, self.now - 60)] + 60.001)
            self.dispatch_at = t
            self.at(t, self.dispatch)

    def ready(self, v, gen):
        if v.gen == gen and v.batch is not None:
            self.fill(v)

    def fill(self, v):
        B = v.batch
        while v.free > 0:
            j = B.take(v.type, v.free)
            if j is None:
                break
            v.free -= j[1]
            self.at(self.now + j[0], self.done, v, j, v.gen)

    def done(self, v, j, gen):
        B = v.batch
        v.free += j[1]
        v.busy += j[0] * j[1] / v.slots
        self.book("busy", self.now - j[0], self.now, v, j[1] / v.slots)
        B.left -= 1
        B.done_t.append(self.now - B.t0)
        if B.left == 0:
            B.end = self.now
            self.ended(B)
            self.running.remove(B)
            for w in list(B.vms):
                if w.batch is B:
                    self.release(w)
            return
        self.fill(v)

    def release(self, v):
        B = v.batch
        v.held_s += self.now - v.lease_t
        self.book("held", v.lease_t, self.now, v)
        B.slots[v.type] -= v.slots
        v.batch, v.free_t, v.gen = None, self.now, v.gen + 1
        v.free = v.slots
        tr = B.b.get("track", B.b["run"])
        self.held[tr] -= 1
        self.peaks.setdefault(tr, []).append((self.now, self.held[tr]))
        idle = self.p.get("idle", 60)
        if self.p.get("demand"):
            idle = max(idle, self.demand_idle(v, B, tr))
        if v.fleet:
            idle = max(idle, self.p["fleet"]["quiet"])
        if self.p.get("adaptive") and self.short_projected():
            idle = self.p["adaptive"]["long"]
        if self.p.get("idle_scarce") and self.left() < self.p["scarce_below"]:  # starts short: a VM kept up is cheaper
            idle = self.p["idle_scarce"]
        if self.p.get("floor"):
            kept = sum(1 for w in self.upfree.get(v.type, {}).values() if w.stop_at - self.now > idle + 1)
            if kept < self.p["floor"]:
                idle = max(idle, self.p["floor_T"])
        v.stop_at = self.now + idle
        self.upfree.setdefault(v.type, {})[v.id] = v
        self.at(v.stop_at, self.stop, v, v.gen)
        if v.type != self.main:
            return
        if self.waiting:
            W = self.waiting.pop(0)
            W.waited = self.now - W.t0
            self.lease(v, W, warm=True)
            if any(k > 0 for t, k in W.want.items() if t != self.main):  # its large VM: a start, or Modal (strand)
                self.pending.append(W)
                self.dispatch()
            return
        if self.p.get("topup"):
            best = None
            for C in self.running:
                if C is not B and C.vms and not C.enough(self.main):
                    q = C.qn.get(self.main, 0) / max(1, C.slots.get(self.main, 0))
                    if best is None or q > best[0]:
                        best = (q, C)
            if best:
                self.lease(v, best[1], warm=True)

    def wake_fleet(self, B):
        """The core fleet (`fleet`: k VMs of the batch type, kept up until `quiet` s pass with no batch): a batch's
        arrival keeps the free ones up `quiet` s more, and brings the fleet back to k (the batch's own starts first,
        the rest started free) within the starts left."""
        f = self.p["fleet"]
        for w in self.upfree.get(self.main, {}).values():
            if w.fleet:
                w.stop_at = max(w.stop_at, self.now + f["quiet"])
        alive = sum(1 for w in self.vms if w.fleet and w.up)
        missing = f["k"] - alive
        if missing <= 0:
            return
        B.fleet_n = min(missing, B.want.get(self.main, 0))
        for _ in range(min(missing - B.fleet_n, self.left(), max(0, self.minute_room()))):
            stopped = self.stopped.get(self.main)
            v = stopped.pop() if stopped else VMx(len(self.vms), self.main)
            if not stopped and v.id == len(self.vms):
                self.vms.append(v)
            self.starts.append(self.now)
            self.active += 1
            v.up, v.ever, v.fleet, v.batch, v.gen = True, True, True, None, v.gen + 1
            v.free_t, v.stop_at = self.now, self.now + f["quiet"]
            self.upfree.setdefault(v.type, {})[v.id] = v
            self.at(v.stop_at, self.stop, v, v.gen)

    def demand_idle(self, v, B, tr):
        """How long a released VM stays up for its client's declared work: a bar while its queue has launches left
        (until the last one starts), a lane session for its heartbeat after each batch; at most `long`, and only while
        the VMs kept for that client are fewer than it held at its peak in the last `window` s (its recent demand)."""
        dm = self.p["demand"]
        if B.b.get("src") == "bar":
            until = self.last_start.get(tr, 0) + 60 if self.last_start.get(tr, 0) > self.now else None
        else:
            until = self.now + dm["hb"] if dm.get("hb") else None
        if until is None:
            return 0
        pk = self.peaks.get(tr, [])
        while len(pk) > 1 and pk[1][0] < self.now - dm.get("window", 600):
            pk.pop(0)
        want = min(dm.get("max", 10**6), max((h for _, h in pk), default=0))
        kept = sum(1 for w in self.upfree.get(v.type, {}).values() if w.owner == tr and w.stop_at > self.now + 60)
        if kept >= want:
            return 0
        v.owner = tr
        return min(dm["long"], until - self.now)

    def stop(self, v, gen):
        if v.gen == gen and v.batch is None and v.up and v.stop_at > self.now + 1e-6:  # (a fleet VM kept up longer)
            self.at(v.stop_at, self.stop, v, gen)
            return
        if v.gen == gen and v.batch is None and v.up:
            v.tail_s += self.now - v.free_t
            self.book("tail", v.free_t, self.now, v)
            v.up, v.free_t = False, None
            self.upfree[v.type].pop(v.id, None)
            self.stopped.setdefault(v.type, []).append(v)
            self.active -= 1

    # ------------------------------------------------------------------ the figures
    def report(self):
        rows = []
        for B in self.batches:
            b = B.b
            rows.append({"run": b["run"], "t0": B.t0, "wall": round((B.end if B.end is not None else self.now) - B.t0, 1), "starts": B.starts,
                         "warm": B.warm, "vms": len({v.id for v in B.vms}), "modal": B.modal, "jobs": len(b["jobs"]),
                         "slot_s": round(sum(j[0] * j[1] for j in b["jobs"]), 1), "waited": round(B.waited, 1),
                         "modal_dollars": round((sum(j[0] for j in b["jobs"]) if B.modal else B.modal_seconds) * modal_rate(b), 4),
                         "modal_part": B.modal_jobs, "done": B.end is not None})
        mult = lambda v: TYPES[v.type][1]
        busy = sum(v.busy * mult(v) for v in self.vms)
        held = sum(v.held_s * mult(v) for v in self.vms)
        tail = sum(v.tail_s * mult(v) for v in self.vms)
        days = {}
        for t in self.starts:
            k = int(t // 86400)
            days[k] = days.get(k, 0) + 1
        return {"starts": len(self.starts), "max_hour_starts": max_window(self.starts, 3600), "batches": len(rows),
                "max_minute_starts": max_window(self.starts, 60), "max_day_starts": max_window(self.starts, 86400), "starts_by_day": days,
                "others": len(self.others), "acct_max_day": max_window(sorted(self.starts + self.others), 86400), "acct_max_hour": max_window(sorted(self.starts + self.others), 3600),
                "fleet_up_vm_h": round(sum(v.held_s + v.tail_s for v in self.vms if v.fleet) * TYPES[self.main][1] / 3600, 1),
                "fleet_busy": round(sum(v.busy for v in self.vms if v.fleet) / max(1, sum(v.held_s + v.tail_s for v in self.vms if v.fleet)), 3),
                "boat_slot_h": round((sum(x["slot_s"] for x in rows if not x["modal"]) - sum(B.modal_seconds for B in self.batches if not B.modal)) / 3600, 1),
                "tiny_modal": sum(1 for B in self.batches if B.tiny and B.modal), "tiny_warm": sum(1 for B in self.batches if B.tiny and not B.modal),
                "modal_batches": sum(r["modal"] for r in rows), "modal_jobs": sum(r["jobs"] if r["modal"] else r["modal_part"] for r in rows), "unfinished": sum(not r["done"] for r in rows),
                "modal_dollars": round(sum(r["modal_dollars"] for r in rows), 3),
                "busy_vm_h": round(busy / 3600, 2), "in_batch_idle_vm_h": round((held - busy) / 3600, 2), "tail_idle_vm_h": round(tail / 3600, 2),
                "boat_dollars": round((held + tail) * VM_DOLLARS_S, 3), "idle_dollars": round((held - busy + tail) * VM_DOLLARS_S, 3), "rows": rows}


def max_window(starts, span):
    s = sorted(starts)
    best, k = 0, 0
    for i, t in enumerate(s):
        while s[k] <= t - span:
            k += 1
        best = max(best, i - k + 1)
    return best


def load(path):
    """The mix, one row per batch (a run whose backends.json repeats another's batch is the same batch)."""
    mix, seen = [], set()
    import gzip
    for b in json.load(gzip.open(path) if str(path).endswith(".gz") else open(path)):
        key = b.get("batch") or b["run"]
        if key in seen:
            continue
        seen.add(key)
        mix.append(b)
    return mix


BASE = {"idle": 60, "share": 1 / 4, "min_budget": 2, "check_resume": True, "topup": True, "wait": 600}
# the chosen policy: BASE, and a released VM up 900 s instead of 60 only when, at the last hour's pace, the starts
# left (hour and day) run out within those 900 s (modal/boat.py's release_idle)
# and (the coordinator's decisions) at most 30 starts a batch, the last 60 of the day and 15 of the hour kept for the
# account's other project
NEW100 = dict(BASE, adaptive={"exhaust": True, "long": 900}, cap=30, reserve=(60, 15))  # the $100 plan's choice
# the $500 choice of c985479 (wall time first, tune-500.txt): released VMs up 300 s, at most 50 a batch
NEW300 = dict(BASE, idle=300, cap=50, reserve=(60, 15))
# the defaults (boat's terms, TOS-6: no idle compute parked to save starts): released VMs up 60 s, a quarter of the
# starts left and at most 50 a batch (the coordinator's choice from the real CHC runs: 725.1 s on 50 VMs against
# 1,116.4 s on 30), the reserve, and with no start left a wait within --max-wait (120 s) for a released VM, then Modal
NEW = dict(BASE, idle=60, cap=50, reserve=(60, 15), wait=MAX_WAIT)
NEW30 = dict(NEW, cap=30)
OLDNEW = {"idle": 300, "idle_scarce": 900, "scarce_below": 100, "share": 1 / 4, "min_budget": 2, "check_resume": True, "topup": True, "wait": 600}
# Lane P (10-31): the $500 plan, the account shared with another project, our starts frugal. week.json.gz is every
# launch of 10-28 to 10-31 (launches.py: the bar's groups, the lanes' checks; all of them ran on Modal), replayed as
# if each had asked the pool first (`--backend auto`).
CEIL = dict(ceil=(0.5, 0.4, 25), dyn=True)  # at most half the plan's day, 40% of its hour, 25 a minute; reserve max(60/15, 2x the other's)
DEMAND = dict(demand={"long": 600, "hb": 300, "window": 600})  # bar: while its queue has launches; lanes: a 300 s heartbeat
TINY = dict(tiny=(4, 10))  # 4 jobs or fewer, or under 10 slot-minutes: a VM already up, else Modal
WEEK = {
    "now: idle 60, 1/4 of the starts left, cap 50, reserve 60/15": NEW,
    "(a) idle 120": dict(NEW, idle=120),
    "(a) idle 300": dict(NEW, idle=300),
    "(a) idle 600": dict(NEW, idle=600),
    "(b) demand-backed idle (<= 600 s, warm <= recent peak)": dict(NEW, **DEMAND),
    "(b2) demand, the bar only (no lane heartbeat)": dict(NEW, demand={"long": 600, "hb": 0, "window": 600}),
    "(c) large VMs": dict(NEW, vm="large"),
    "(c2) xlarge VMs": dict(NEW, vm="xlarge"),
    "(d) tiny batches: warm VM or Modal": dict(NEW, **TINY),
    "(e) ceiling 50/40/25 + dynamic reserve": dict(NEW, **CEIL),
    "c+d+e": dict(NEW, vm="large", **TINY, **CEIL),
    "b+d+e": dict(NEW, **DEMAND, **TINY, **CEIL),
    "b+c+d+e": dict(NEW, vm="large", **DEMAND, **TINY, **CEIL),
    "b2+c+d+e": dict(NEW, vm="large", demand={"long": 600, "hb": 0, "window": 600}, **TINY, **CEIL),
    "a300+c+d+e": dict(NEW, vm="large", idle=300, **TINY, **CEIL),
    "a600+c+d+e": dict(NEW, vm="large", idle=600, **TINY, **CEIL),
    # a lower ceiling: room for the other project's growth
    **{f"b+c+d+e, ceiling {round(100 * d)}/{round(100 * h)}/{m}": dict(NEW, vm="large", **DEMAND, **TINY, ceil=(d, h, m), dyn=True) for d, h, m in ((0.25, 0.2, 15), (0.15, 0.15, 10))},
    **{f"c+d+e, ceiling {round(100 * d)}/{round(100 * h)}/{m}": dict(NEW, vm="large", **TINY, ceil=(d, h, m), dyn=True) for d, h, m in ((0.25, 0.2, 15), (0.15, 0.15, 10))},
    "c2+b+d+e (xlarge)": dict(NEW, vm="xlarge", **DEMAND, **TINY, **CEIL),
    # (the coordinator's) a dedicated-like core fleet of k large VMs, up until 25 min pass with no batch; bursts
    # beyond it start VMs under the ceiling, else Modal
    **{f"fleet {k} large (25 min quiet)+d+e": dict(NEW, vm="large", fleet={"k": k, "quiet": 1500}, **TINY, **CEIL) for k in (4, 8, 12)},
    **{f"fleet {k} large+b+d+e": dict(NEW, vm="large", fleet={"k": k, "quiet": 1500}, **DEMAND, **TINY, **CEIL) for k in (4, 8, 12)},
}
POLICIES = {
    **WEEK,
    "old": {"idle": 60},
    "new": NEW,
    "new for $100 (cap 30, 60 s idle, 900 s when short)": NEW100,
    "c985479 ($500: 300 s idle, cap 50)": NEW300,
    "new with cap 30": NEW30,
    "base (new without the longer idle)": BASE,
    "new, no reserve": dict(NEW100, reserve=RESERVE),
    "new, no reserve, no cap": dict(NEW100, reserve=RESERVE, cap=None),
    "idle300/scarce900": OLDNEW,
    # one change at a time
    "old+idle300": {"idle": 300},
    "old+idle600": {"idle": 600},
    "old+idle1800": {"idle": 1800},
    "old+cap80": {"idle": 60, "cap": 80},
    "old+cap40": {"idle": 60, "cap": 40},
    "share1/2": {"idle": 60, "share": 1 / 2, "check_resume": True},
    "share1/4": {"idle": 60, "share": 1 / 4, "check_resume": True},
    "share1/8": {"idle": 60, "share": 1 / 8, "check_resume": True},
    "share1/4+topup": {"idle": 60, "share": 1 / 4, "check_resume": True, "topup": True},
    "share1/4+topup+wait600": {"idle": 60, "share": 1 / 4, "check_resume": True, "topup": True, "wait": 600},
    # the idle window on top
    "share1/4+topup+wait600+idle300": {"idle": 300, "share": 1 / 4, "check_resume": True, "topup": True, "wait": 600},
    "share1/4+topup+wait600+idle600": {"idle": 600, "share": 1 / 4, "check_resume": True, "topup": True, "wait": 600},
    "share1/4+topup+wait600+idle120+floor16/1800": {"idle": 120, "share": 1 / 4, "check_resume": True, "topup": True, "wait": 600, "floor": 16, "floor_T": 1800},
    "share1/4+topup+wait600+idle120+floor32/1800": {"idle": 120, "share": 1 / 4, "check_resume": True, "topup": True, "wait": 600, "floor": 32, "floor_T": 1800},
    "share1/4+topup+wait600+idle300+floor16/1800": {"idle": 300, "share": 1 / 4, "check_resume": True, "topup": True, "wait": 600, "floor": 16, "floor_T": 1800},
    "share1/4+topup+wait600+idle120/scarce600": {"idle": 120, "idle_scarce": 600, "scarce_below": 100, "share": 1 / 4, "check_resume": True, "topup": True, "wait": 600},
    "share1/4+topup+wait600+idle60/scarce900": {"idle": 60, "idle_scarce": 900, "scarce_below": 100, "share": 1 / 4, "check_resume": True, "topup": True, "wait": 600},
    "share1/4+topup+wait600+idle300/scarce900": {"idle": 300, "idle_scarce": 900, "scarce_below": 100, "share": 1 / 4, "check_resume": True, "topup": True, "wait": 600},
    "base+exhaust600": dict(BASE, adaptive={"exhaust": True, "long": 600}),
    "base+exhaust900": dict(BASE, adaptive={"exhaust": True, "long": 900}),
    "base+exhaust1800": dict(BASE, adaptive={"exhaust": True, "long": 1800}),
    "base+exhaust3600": dict(BASE, adaptive={"exhaust": True, "long": 3600}),
    "base+adapt H2/600": dict(BASE, adaptive={"H": 2, "long": 600}),
    "base+adapt H4/600": dict(BASE, adaptive={"H": 4, "long": 600}),
    "base+adapt H8/600": dict(BASE, adaptive={"H": 8, "long": 600}),
    "base+adapt H4/1800": dict(BASE, adaptive={"H": 4, "long": 1800}),
    "base+adapt H8/1800": dict(BASE, adaptive={"H": 8, "long": 1800}),
    "base+adapt H4/1800+hour": dict(BASE, adaptive={"H": 4, "long": 1800, "hour": True}),
    "base+adapt H4/600+hour": dict(BASE, adaptive={"H": 4, "long": 600, "hour": True}),
    "base+adapt H8/1800+hour": dict(BASE, adaptive={"H": 8, "long": 1800, "hour": True}),
    "share1/3+topup+wait600+idle300": {"idle": 300, "share": 1 / 3, "check_resume": True, "topup": True, "wait": 600},
    "share1/8+topup+wait600+idle300": {"idle": 300, "share": 1 / 8, "check_resume": True, "topup": True, "wait": 600},
    "share1/4cap40+topup+wait600+idle300": {"idle": 300, "share": 1 / 4, "cap": 40, "check_resume": True, "topup": True, "wait": 600},
}


def slowdowns(r, ref):
    """Each batch's wall over its wall with no limits at all (the old sizing, unlimited starts), for those that ran on
    boat in both and had a minute of work or more."""
    by = {x["run"]: x for x in ref["rows"]}
    out = []
    for x in r["rows"]:
        y = by.get(x["run"])
        if y and not x["modal"] and not y["modal"] and y["wall"] > 0 and x["slot_s"] >= 60:
            out.append(x["wall"] / y["wall"])
    return out


def week_line(name, r, ref):
    """One row of the Lane P table: our starts (a day each, the peaks), what is left of the plan for the other
    project, idle VM-hours (default-VM hours, as the plan counts them), Modal's share, the slowdown."""
    sd = sorted(slowdowns(r, ref))
    q = lambda p: round(sd[min(len(sd) - 1, int(p * len(sd)))], 2) if sd else None
    days = r["starts_by_day"]
    by = {x["run"]: x for x in ref["rows"]}
    big = sorted(x["wall"] / by[x["run"]]["wall"] for x in r["rows"] if x["jobs"] >= 1000 and x["run"] in by and by[x["run"]]["wall"] > 0 and not x["modal"])
    bigm = sum(1 for x in r["rows"] if x["jobs"] >= 1000 and x["modal"])
    per = "/".join(str(days.get(k, 0)) for k in sorted(days)) if days else "0"
    return (f"{name:56} starts/day {per:>16}  peak 24h {r['max_day_starts']:4} hour {r['max_hour_starts']:3} min {r['max_minute_starts']:2}"
            f"  left for others: day {1680 - r['max_day_starts']:4} hour {420 - r['max_hour_starts']:3}"
            f"  idle VM-h {round(r['in_batch_idle_vm_h'] + r['tail_idle_vm_h'], 1):6} (after release {r['tail_idle_vm_h']:6}) of {round(r['boat_dollars'] / 0.036)}"
            f"  boat slot-h {r['boat_slot_h']:6} ({round(r['boat_slot_h'] / max(1, r['starts']), 2)} a start)"
            f"  modal {r['modal_batches']:4} batches {r['modal_jobs']:6} jobs ${r['modal_dollars']:7.2f} (tiny {r['tiny_modal']}, tiny warm {r['tiny_warm']})"
            f"  wall/unlimited median {q(0.5)} p90 {q(0.9)}; fan-outs of 1000+ jobs: {len(big)} on boat, median {round(big[len(big) // 2], 2) if big else None}"
            f" max {round(big[-1], 2) if big else None}, {bigm} on Modal" + (f"; fleet {r['fleet_up_vm_h']} VM-h up, {round(100 * r['fleet_busy'])}% busy" if r.get("fleet_up_vm_h") else ""))


def line(name, r, ref):
    sd = sorted(slowdowns(r, ref))
    q = lambda p: round(sd[min(len(sd) - 1, int(p * len(sd)))], 2) if sd else None
    return (f"{name:46} starts {r['starts']:4} (most in an hour {r['max_hour_starts']:3})  modal {r['modal_batches']:2} batches {r['modal_jobs']:5} jobs ${r['modal_dollars']:6.3f}"
            f"  boat ${r['boat_dollars']:6.3f} (idle ${r['idle_dollars']:.3f}: {r['in_batch_idle_vm_h']} in batches + {r['tail_idle_vm_h']} after, VM-h)"
            f"  wall/unlimited: median {q(0.5)} p90 {q(0.9)} max {q(1.0) if not sd else round(sd[-1], 2)}")


BIG = ["runs/backends/chc-gdp", "runs/step/chc-base", "runs/backends/tip-gdp3", "runs/backends/term-gdp", "runs/backends/suite-default", "runs/table/chc", "runs/table/tip", "runs/table/term"]

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("mix")
    ap.add_argument("--policy", action="append", default=[])
    ap.add_argument("--plan", default="500")
    ap.add_argument("--rows", action="store_true")
    ap.add_argument("--since", default="")
    ap.add_argument("--until", default="")
    ap.add_argument("--other", type=float, default=0, help="the other project's starts a day")
    a = ap.parse_args()
    mix = load(a.mix)
    import datetime
    iso = lambda x: datetime.datetime.fromisoformat(x.replace("Z", "+00:00")).timestamp()
    mix = [b for b in mix if (not a.since or b["start"] >= iso(a.since)) and (not a.until or b["start"] < iso(a.until))]
    if a.since or a.other:  # Lane P's table
        ref = Sim(mix, POLICIES["old"], "inf").run().report()
        print(f"{len(mix)} batches, {sum(len(b['jobs']) for b in mix)} jobs, {round(sum(j[0] * j[1] for b in mix for j in b['jobs']) / 3600, 1)} slot-hours of work;"
              f" plan ${a.plan}: {PLANS[a.plan][:3]} starts a minute, hour, day; the other project {a.other} a day")
        print(week_line("unlimited starts (the reference)", ref, ref))
        for name in a.policy or WEEK:
            r = Sim(mix, POLICIES[name], a.plan, other=a.other).run().report()
            print(week_line(name, r, ref), flush=True)
        sys.exit(0)
    ref = Sim(mix, POLICIES["old"], "inf").run().report()
    print(f"{len(mix)} batches, {sum(len(b['jobs']) for b in mix)} jobs, {round(sum(j[0] * j[1] for b in mix for j in b['jobs']) / 3600, 1)} slot-hours of work;"
          f" plan ${a.plan}: {PLANS[a.plan][:3]} starts a minute, hour, day")
    print(line("unlimited starts (the reference)", ref, ref))
    for name in a.policy or POLICIES:
        r = Sim(mix, POLICIES[name], a.plan).run().report()
        print(line(name, r, ref))
        big = {x["run"]: x for x in r["rows"]}
        print("    " + "  ".join(f"{k.split('/')[-1]} {'modal' if big[k]['modal'] else str(round(big[k]['wall'])) + ' s/' + str(big[k]['vms'])}" for k in BIG if k in big))
        if a.rows:
            for x in r["rows"]:
                print(f"      {x['run']:40} wall {x['wall']:7} starts {x['starts']:4} warm {x['warm']:3} vms {x['vms']:4} waited {x['waited']:6} {'MODAL' if x['modal'] else ''}")
