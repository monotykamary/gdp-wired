# gdp-wired modal: experiments in parallel

| File | What |
| --- | --- |
| `run.py` | A job list fanned out on Modal, one container per job (bun and Lean 4.34.0 in the image, gdp-wired mounted fresh each run). Logs land in `<out>/<name>.log`, `summary.tsv` has exit codes and seconds (and, 4th, the backend that ran the job) |
| `suite.json` | Every runner and probe, plus the soundness fuzz as 32 seeds (`FUZZ_SEED`), about 10 minutes of wall time for over 3 hours of job time |
| (cache) | The Lean twin's library is compiled once per version of its sources: `run.py` keeps the `.olean` files on the `gdp-wired-olean` volume under a hash of every library source and the toolchain, copies them into a job before it runs and saves the ones it compiled; the suite's commands skip a library compile whose file is there (`[ -f X.olean ] ||`), except the compiles whose output a job checks |
| `reap.sh` | Stops apps whose client died (each run registers its app id and client pid in `.live/`); live runs and other apps are only listed. Then the same for boat VMs and RunPod pods |
| `fanout.py` | One interface over three providers (`--backend`): boat.dev VMs for CPU work, RunPod pods for GPU work, Modal for the rest and as the fallback of both |
| `boat.py` | The boat backend: the image, the pool, a batch's VMs, the scheduler; `python3 modal/boat.py status \| reap \| teardown \| image [--build] \| usage <since>` |
| `agent.py` | What runs on each boat VM (stdlib Python): unpacks a batch's tree, runs items in mount namespaces of their own, reports, kills |
| `runpod.py` | The RunPod backend: one pod per batch, prepared once, deleted however the batch ends; `python3 modal/runpod.py batch \| reap \| status` |

GPU runs have their own runners: `../research/modal-gpu/run_gpu.py` (the Handwired searches) and `../research/synth/run_gpu.py`
(invariant and rank synthesis), both through Dawn on NVIDIA's Vulkan driver.

```sh
cd gdp-wired && modal run modal/run.py --jobs modal/suite.json --out ../runs/modal/suite && sh modal/reap.sh
# a quick run: the generated Lean checked by native_decide (compiled Lean; a release runs without the flag)
cd gdp-wired && modal run modal/run.py --jobs modal/suite.json --out ../runs/modal/quick --native && sh modal/reap.sh
```

Cost hygiene: jobs time out at 15 minutes unless they ask for more (the command is killed inside the container first,
so its output still comes back), every spawned call is cancelled when the client exits for any reason, and after every
batch `reap.sh` (or `modal app list`) confirms nothing is left running. Never stop a client with a broad `pkill -f`.

## Backends: boat, RunPod, Modal

```sh
python3 modal/run.py --backend auto --jobs modal/suite.json --out runs/backends/suite          # CPU: boat, else Modal
python3 compare/chc/modal_chc.py --backend auto --out runs/backends/chc --tools gdp            # the same for a runner
python3 research/hw/run_gpu.py --backend auto --out runs/backends/hw.json --args=--hand        # GPU: RunPod, else Modal
python3 modal/run.py --backend boat ...      # force boat (no fallback); --backend runpod for a GPU runner; modal as before
```

`--backend modal` stays the default. `auto` sends CPU work to boat and GPU work to RunPod, and Modal takes over when the
primary can't serve: before a batch starts, the whole batch (the provider's API unreachable or erroring, its billing,
no capacity: boat with no VM to be had within its active-VM and start limits, or its image not built; RunPod out of
every GPU type in the list, in the secure cloud then the community cloud; a RunPod balance under
`$GDPW_RUNPOD_MIN_BALANCE`, default 5); during a batch, each job whose VM or pod died, after one more try on the primary.
With `--max-wait` (120 s), a batch that has no boat VM ready by then goes to Modal. Every move is in the final line (`4
jobs, 0 failed, ... ; 4 on modal (fallback: 4 jobs: no boat starts left this hour or day)`), in `<out>/backends.json`
and, for a GPU runner, in `<out>.backend.json`; the results are the same files in the same format whichever ran them.
From plain `python3` the scripts run again under the interpreter of the `modal` CLI, so Modal can take over.

**boat** (CPU). A pool of VMs that lives across batches and across worktrees (its registry is the main checkout's
`modal/.live/boat-pool.json`, under a lock): a batch leases free VMs (its pid on each), resumes the stopped ones,
creates the rest from the image within the plan's limits (`boat limits`, read at every batch), and releases them at
the end; boat stops a released VM after `--idle` seconds (60) unless another batch takes it, so back-to-back batches
reuse running VMs, and stopped VMs bill no compute. `--teardown` deletes the batch's VMs instead;
`python3 modal/boat.py teardown [--all | --type large]` deletes free ones. Each VM is 4 vCPU and 8 GB: two slots of
2 vCPU and 4 GB (Modal's container), a job of 4 vCPU or 8 GB a whole VM, the one job that asks for 8 vCPU and 16 GB a
`large` VM. Jobs start longest first by the last run's times (`--durations`: a `summary.tsv`, or a runner's
`results.jsonl`; for `run.py` else the newest `summary.tsv` with the same jobs), each in a mount namespace of its own: a private `/tmp`, a fresh copy of the
batch's tree at `/work/gdp-wired` (as on Modal), its runner's paths (`/bench`), its own CPUs (`taskset`, so `nproc` is
its share), under `timeout -s KILL`.

- The image is one named snapshot, `gdpw-<hash>`, built in layers (bun and Lean 4.34.0 as `run.py`'s image, then each
  compare runner's `BOAT_SETUP`: TIP's tools and solvers, CHC's, the ITS', SV-COMP's), each a snapshot of its own, so a
  changed layer rebuilds only itself and those above it (`python3 modal/boat.py image --build`; under `--backend boat`
  a missing image is built first, under `auto` its batch goes to Modal). The current image and the one before are kept;
  older snapshots, and the free VMs made from them, are deleted.
- A batch's tree is what git sees (tracked and untracked files that aren't ignored, the submodules' too, minus the
  paths `run.py` leaves out): one VM gets it, serves it to the others through a token-gated boat URL, and every VM
  unpacks it fresh, so no job sees an earlier batch's tree. The Lean library's `.olean` files stay on each VM's disk
  under the library's key; one VM's set comes back here after a batch (`.live/olean/<key>/`) and goes to the VMs that
  lack it next time.
- boat keeps a stopped VM's disk 14 days: a VM whose disk expired, or that stopped without a snapshot, is deleted and
  replaced from the image; a VM stopped for 12 days is resumed and stopped again when a batch runs.
- Starts: boat counts a creation **and a resume** as a start (its 429: "create, fork and resume each count as one
  start"; the $100 plan: 30 a minute, 210 an hour, 840 a day, 300 VMs up). Only a VM still up within its idle time
  comes without one, so the pool spares boot time and keeps caches warm, not starts. A batch's size follows the work
  (enough VMs that its longest job bounds it), the start rate (VMs arriving over time: about sqrt(2 r W / c)) and the
  starts left; with none left, `auto` sends the batch to Modal.
- Safety: every VM a batch holds has a TTL of 15 minutes, renewed while the client lives, so a VM whose client died
  stops by itself; Ctrl-C, SIGTERM and SIGHUP kill the batch's jobs and release its VMs; `reap.sh` releases leases of
  dead clients, kills what they left running and stops VMs left up past their idle time.

**RunPod** (GPU). One pod per batch (the GPU types in order: `--gpus`, `$GDPW_RUNPOD_GPUS`, else 4090, L4, A5000, 3090,
...), `runpod-ubuntu-2404` with Dawn's node bindings, bun and NVIDIA's Vulkan driver through its EGL library (the stock
ICD, `libGLX_nvidia`, needs an X server); `vulkaninfo --summary` must list an NVIDIA device before anything runs. The
runner's own function runs on the pod in the Modal image's paths, so its output is the Modal run's. The pod is deleted
in a finally; `modal/.live/runpod-<name>.json` holds its name and the client's pid meanwhile, and `reap.sh` deletes a
pod whose client is gone and any `gdpw-` pod with no ticket.

Measured (each figure from the run named; boat's dollars from `boat usage`, Modal's from `modal billing report` for the
run's app):

| Work | boat / RunPod | Modal |
| --- | --- | --- |
| The suite, 200 jobs | 0 failed, 267.7 s wall, 3,002.5 s of job time, $0.032 (`runs/backends/suite-default`) | 0 failed, 489.8 s, 4,246.7 s, $0.256 (`runs/modal/backends/suite-default`) |
| The suite, `--usual` | 0 failed, 248.4 s, 2,420.4 s, $0.028 (`runs/backends/suite-usual`) | 0 failed, 489.8 s, 4,042.3 s, $0.237 (`runs/modal/backends/suite-usual`) |
| CHC, gdp on 1,406 tasks | 387 solved, none wrong, 802.4 s wall (the results in by 482 s), $0.405, 192 VMs (`runs/backends/chc-gdp`) | 381 solved, none wrong, 330.1 s, $2.604 (`runs/modal/arith/chc-gdp`) |
| TIP, gdp on 492 + 68 | 140 proven, none wrong, 333.9 s, $0.210, 119 VMs (`runs/backends/tip-gdp3`) | 140 proven, none wrong, 270.2 s, $0.633 (`runs/modal/arith/tip-gdp`) |
| ITS (TermComp), gdp on 1,239 | 380 answered, none contradicting Modal's, 381.5 s, $0.392, 170 VMs (`runs/backends/term-gdp`) | 377, 305.8 s, $2.122 (`runs/modal/backends/term-gdp`) |
| Handwired search `--hand` | RTX 4090, the same results (`runs/backends/gpu/hw-hand-runpod.json`) | L4 (`runs/modal/backends/gpu/hw-hand-l4.json`) |

A boat vCPU is faster than a Modal one (the suite's jobs in 71% of Modal's job time, 60% with `--usual`), so a fixed
limit (60 s) can let it solve more: that is the machine, not the prover. More tasks reach the hard limit there instead
of the solver's own answer just before it (timeout: CHC 53 against 8, TIP 136 against 177, ITS 113 against 30).
The batches above were sized by the plan's limits of the day ($100: 30 starts a minute, 210 an hour), so a large one
spends minutes bringing VMs up (`bring_up_s` in each `backends.json`; the TIP one counts the wait for starts too). A `large` VM (8 vCPU) ran the same eight jobs, four at a time, in 1.76
times the job time of two default VMs, two at a time (`runs/backends/large-test`): per unit of work it costs 1.7 times
as much, so the pool uses default VMs and a large one only for a job that needs 16 GB.
