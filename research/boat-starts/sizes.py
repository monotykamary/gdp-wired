"""The wall-time cost of fewer VMs for the three big compare runs: each alone on n VMs (n of them started at 30 a
minute, two slots each, longest call first), the time from its first VM request to its last call's end, against
the old policy's run on its measured VM count (calibrate.py: the model's error there is under half a minute).

    python3 research/boat-starts/sizes.py research/boat-starts/mix.json > research/boat-starts/sizes.txt
"""
import sys

sys.path.insert(0, __import__("os").path.dirname(__file__))
import sim

mix = {b["run"]: b for b in sim.load(sys.argv[1])}
RUNS = {"CHC (gdp, 1,406 tasks)": ("runs/backends/chc-gdp", 192), "TIP (gdp, 560 calls of a whole VM)": ("runs/backends/tip-gdp3", 119),
        "termination (gdp, 1,239 ITS tasks)": ("runs/backends/term-gdp", 170)}
print("run                                  measured VMs   sim wall at:  n=20   n=40   n=50   n=80   n=120  n=190   (s; sum of call seconds / 2 slots = the work)")
for name, (run, measured) in RUNS.items():
    b = dict(mix[run], start=0.0)
    walls = []
    for n in (20, 40, 50, 80, 120, 190):
        s = sim.Sim([b], {"idle": 60, "force": n}, "minute", stopped=n).run()
        walls.append(round(max(s.batches[0].done_t)))
    work = sum((j[0] + sim.OVERHEAD["runner"]) * j[1] for j in b["jobs"])
    print(f"{name:38} {measured:4}          " + "  ".join(f"{w:5}" for w in walls) + f"   ({round(work)} slot-s)")
