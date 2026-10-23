"""The sim's timing model against the old policy's measured runs: each run alone, on as many VMs as it had (its
resumes from a pool of stopped VMs, the rest created, 30 starts a minute), against its log's progress lines (the time
when k of its calls had finished, from the runner's start; the first VM's setup and the runner's task listing come
before the calls, S seconds fitted per run kind). Prints, per OVERHEAD and BOOT, each run's sim and measured times.

    python3 research/boat-starts/calibrate.py research/boat-starts/mix.json > research/boat-starts/calibrate.txt
"""
import itertools
import json
import sys

import sim

# progress lines of the runs' logs: (calls done, seconds since the runner's start), and the VMs they had
RUNS = {
    "runs/backends/chc-gdp": {"vms": 192, "resumed": 12, "progress": [(100, 184), (200, 241), (300, 247), (400, 301), (500, 307), (600, 361), (700, 367), (800, 421), (900, 427), (1000, 451), (1100, 460), (1200, 467), (1300, 469), (1400, 482)]},
    "runs/step/chc-base": {"vms": 84, "resumed": 84, "progress": [(100, 145), (200, 200), (300, 213), (400, 236), (500, 281), (600, 317), (700, 350), (800, 384), (900, 422), (1000, 453), (1100, 476), (1200, 502), (1300, 539), (1400, 574)]},
    "runs/backends/tip-gdp3": {"vms": 119, "resumed": 119, "progress": [(100, 245), (200, 281), (300, 287), (400, 289), (500, 291)]},
    "runs/backends/term-gdp": {"vms": 140, "resumed": 89, "progress": [(200, 184), (400, 246), (600, 303), (800, 311), (1000, 315), (1200, 332)]},
}

mix = {b["run"]: b for b in sim.load(sys.argv[1])}
print("run                       S(fit)  sim − measured at each progress line (s)            mean |err|")
for boot, oh in itertools.product([10, 30, 60], [0, 2, 5]):
    sim.BOOT, sim.OVERHEAD = float(boot), {"run.py": 0.0, "runner": float(oh)}
    print(f"BOOT {boot} s, OVERHEAD {oh} s a call")
    for run, o in RUNS.items():
        b = dict(mix[run], start=0.0)
        s = sim.Sim([b], {"idle": 60, "force": o["vms"]}, "minute", stopped=o["resumed"]).run()
        done = sorted(s.batches[0].done_t)
        simt = [done[k - 1] for k, _ in o["progress"]]
        meas = [t for _, t in o["progress"]]
        S = sum(m - x for m, x in zip(meas, simt)) / len(meas)  # the setup that fits best (least squares)
        err = [round(x + S - m) for x, m in zip(simt, meas)]
        print(f"  {run.split('/')[-1]:22} {S:6.1f}  {err}  {round(sum(map(abs, err)) / len(err), 1)}")
