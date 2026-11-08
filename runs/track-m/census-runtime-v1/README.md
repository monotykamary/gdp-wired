# First runtime-isolation attempt — partial retained evidence only

The eight-process job exited successfully on the same exclusive VM, but the
full CPU profiles exceeded the scheduler's retained stdout window. The beginning
of `runtime-controls.log`, including `measurements.json`, is missing. This is
**not** a complete eight-process timing dataset and is excluded from aggregate
validation and conclusions.

The retained `p2`, `s1` and `s2` law records each show three checked results.
In particular, disabling concurrent JIT still leaves Inv1758 at 9.857 and
7.906 kernel seconds. These partial receipts are retained, not silently replaced.

`../census-runtime-v2/` repeats the experiment with compact CPU-profile summaries
so its complete structured measurements survive. No proof cap or production
source changed for the repeat; the repair concerns output retention only.
