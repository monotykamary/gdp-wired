"""A job's CPU as the job sees it: the CPU model, `nproc` (its share: boat's agent pins a job to its slot's vCPUs by
taskset), and the seconds of a fixed pure-Python loop, alone and as `nproc` copies at once (two threads of one core
share it: the parallel time shows whether a slot's vCPUs are cores or hyperthreads). Run it on each backend in the
same batch shape and divide.

    python3 research/boat-starts/cpubench.py [N]
"""
import multiprocessing
import os
import subprocess
import sys
import time

N = int(sys.argv[1]) if len(sys.argv) > 1 else 15_000_000


def loop(_=None):
    t, s = time.perf_counter(), 0
    for i in range(N):
        s += i * i
    return time.perf_counter() - t


if __name__ == "__main__":
    info = subprocess.run(["sh", "-c", "lscpu 2>/dev/null | grep -E '^(Model name|CPU\\(s\\)|Thread|Core|Socket)'"], capture_output=True, text=True).stdout
    print(info.strip())
    n = len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else os.cpu_count()
    one = min(loop() for _ in range(3))
    with multiprocessing.Pool(n) as p:
        par = max(p.map(loop, range(n)))
    print(f"cpubench: nproc {n}, one {one:.2f} s, {n} at once {par:.2f} s (slowdown {par / one:.2f})")
