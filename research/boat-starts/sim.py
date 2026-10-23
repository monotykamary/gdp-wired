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

BOOT = 10.0
PREP = {"run.py": 22.0, "runner": 10.0}
OVERHEAD = {"run.py": 0.0, "runner": 5.0}  # calibrate.py: the least error against the old runs' progress lines
VM_DOLLARS_S = 1e-5  # a default VM (4 vCPU): $0.036 an hour; a large one (8 vCPU) twice that
RESERVE = 10
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
    __slots__ = ("id", "type", "slots", "free", "batch", "up", "stop_at", "busy", "held_s", "tail_s", "free_t", "lease_t", "gen", "ever")

    def __init__(self, i, t):
        self.id, self.type = i, t
        self.slots = 4 if t == "large" else 2
        self.free, self.batch, self.up, self.stop_at = self.slots, None, False, None
        self.busy = self.held_s = self.tail_s = 0.0
        self.free_t = self.lease_t = None
        self.gen, self.ever = 0, False


class Batch:
    def __init__(self, b, t0, overhead, prep):
        self.b, self.t0, self.prep = b, t0, prep
        self.q = {}  # (type, weight) -> durations, longest last (popped from the end)
        for j in b["jobs"]:
            self.q.setdefault((j[2], j[1]), []).append(j[0] + overhead)
        for k in self.q:
            self.q[k].sort()
        self.qn = {}  # type -> jobs queued
        for (t, w), xs in self.q.items():
            self.qn[t] = self.qn.get(t, 0) + len(xs)
        self.slots = {}  # type -> slots of the VMs it holds
        self.vms, self.left, self.want = [], len(b["jobs"]), {}
        self.starts = self.warm = 0
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
    def __init__(self, mix, pol, plan="100", stopped=0):
        self.mix, self.p = mix, pol
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
        m = (2 if v.type == "large" else 1) * frac
        while t1 > t0:
            k = int(t0 // 86400)
            e = min(t1, (k + 1) * 86400)
            d = self.days.setdefault(k, {"held": 0.0, "busy": 0.0, "tail": 0.0})
            d[kind] += (e - t0) * m
            t0 = e

    def day_dollars(self, k):
        d = self.days.get(k, {"held": 0.0, "busy": 0.0, "tail": 0.0})
        return round((d["held"] + d["tail"]) * VM_DOLLARS_S, 3), round((d["held"] - d["busy"] + d["tail"]) * VM_DOLLARS_S, 3)

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

    def left(self):
        """Starts left this hour and day after the reserve (what plan_vms and the gate read)."""
        return max(0, min(self.lim_hour - self.count(3600), self.lim_day - self.count(86400)) - RESERVE)

    def room_now(self):
        return max(0, min(self.lim_min - self.count(60), self.left(), self.lim_active - self.active))

    def short_projected(self):
        """Will the starts run out before the work does? At the last hour's pace p (its starts), the day's starts
        left last fewer than H hours, or the hour's left are fewer than p (the pace would spend the hour)."""
        a = self.p["adaptive"]
        p = self.count(3600)
        day_left = self.lim_day - self.count(86400) - RESERVE
        hour_left = self.lim_hour - p - RESERVE
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
        useful = max(1, math.ceil(W / (2 * max(L, 1e-9))))
        useful = min(useful, sum(j[1] for j in items) // 2 + 1, len(items))
        by_rate = up + math.ceil(math.sqrt(2 * (self.lim_min / 60) * W / 2))
        room = self.lim_active - self.active + up
        return max(1, min(useful, by_rate, room, up + self.left()))

    def size(self, items, up):
        if self.p.get("force"):
            return self.p["force"]
        n = self.plan_old(items, up)
        if self.p.get("share") is not None:
            left = self.left()
            budget = min(left, max(self.p.get("min_budget", 2), math.floor(self.p["share"] * left)))
            if self.p.get("cap"):
                budget = min(budget, self.p["cap"])
            n = min(n, up + budget)
        elif self.p.get("cap"):
            n = min(n, self.p["cap"])
        return max(n, 0)

    # ------------------------------------------------------------------ a batch
    def arrive(self, b):
        kind = b["kind"] or "runner"
        B = Batch(b, self.now, OVERHEAD[kind], PREP[kind])
        self.batches.append(B)
        if not b["jobs"]:
            B.end = self.now
            return
        self.running.append(B)
        types = {}
        for j in b["jobs"]:
            types.setdefault(j[2], []).append(j)
        for t, items in types.items():
            up = sorted(self.upfree.get(t, {}).values(), key=lambda v: v.free_t)
            n = self.size(items, len(up)) if t == "default" else len(items)  # (one large VM per job that needs it)
            k = min(n, len(up))
            for v in up[len(up) - k:]:
                self.lease(v, B, warm=True)
            B.want[t] = n - k
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
        if B not in self.waiting and B.enough("default"):
            return
        left = self.left()
        if left > 0 and B not in self.pending:
            lack = math.ceil((B.qn.get("default", 0) - B.slots.get("default", 0)) / 2)
            budget = min(left, max(self.p.get("min_budget", 2), math.floor(self.p.get("share", 1) * left)))
            if B in self.waiting:
                self.waiting.remove(B)
            B.want["default"] = max(0, min(lack, budget))
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
            self.active += 1
        v.batch, v.gen, v.lease_t, v.up, v.free_t, v.ever = B, v.gen + 1, self.now, True, None, True
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
                        if any(k > 0 for t, k in C.want.items() if t != "default"):
                            self.at(max(self.now, C.t0 + MAX_WAIT), self.strand, C)
                        if C.want.get("default", 0) > 0 and self.p.get("topup"):  # short of VMs: asks again later
                            self.at(self.now + RETRY, self.retry, C)
                        C.want = {t: 0 for t in C.want}
                    return
                t = next((t for t, k in B.want.items() if k > 0), None)
                if t is None:
                    self.pending.remove(B)
                    continue
                stopped = self.stopped.get(t)
                # a creation checks whether the batch still needs it; a resume did only under the new policy
                if t == "default" and (not stopped or self.p.get("check_resume")) and B.enough(t):
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
            if self.count(60) >= self.lim_min:
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
        idle = self.p.get("idle", 60)
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
        if v.type != "default":
            return
        if self.waiting:
            W = self.waiting.pop(0)
            W.waited = self.now - W.t0
            self.lease(v, W, warm=True)
            if any(k > 0 for t, k in W.want.items() if t != "default"):  # its large VM: a start, or Modal (strand)
                self.pending.append(W)
                self.dispatch()
            return
        if self.p.get("topup"):
            best = None
            for C in self.running:
                if C is not B and C.vms and not C.enough("default"):
                    q = C.qn.get("default", 0) / max(1, C.slots.get("default", 0))
                    if best is None or q > best[0]:
                        best = (q, C)
            if best:
                self.lease(v, best[1], warm=True)

    def stop(self, v, gen):
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
        mult = lambda v: 2 if v.type == "large" else 1
        busy = sum(v.busy * mult(v) for v in self.vms)
        held = sum(v.held_s * mult(v) for v in self.vms)
        tail = sum(v.tail_s * mult(v) for v in self.vms)
        return {"starts": len(self.starts), "max_hour_starts": max_window(self.starts, 3600), "batches": len(rows),
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
    for b in json.load(open(path)):
        key = b.get("batch") or b["run"]
        if key in seen:
            continue
        seen.add(key)
        mix.append(b)
    return mix


BASE = {"idle": 60, "share": 1 / 4, "min_budget": 2, "check_resume": True, "topup": True, "wait": 600}
# the chosen policy: BASE, and a released VM up 900 s instead of 60 only when, at the last hour's pace, the starts
# left (hour and day) run out within those 900 s (modal/boat.py's release_idle)
NEW = dict(BASE, adaptive={"exhaust": True, "long": 900})
OLDNEW = {"idle": 300, "idle_scarce": 900, "scarce_below": 100, "share": 1 / 4, "min_budget": 2, "check_resume": True, "topup": True, "wait": 600}
POLICIES = {
    "old": {"idle": 60},
    "new": NEW,
    "base (new without the longer idle)": BASE,
    "new+cap30": dict(NEW, cap=30),
    "new+cap50": dict(NEW, cap=50),
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
    ap.add_argument("--plan", default="100")
    ap.add_argument("--rows", action="store_true")
    a = ap.parse_args()
    mix = load(a.mix)
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
