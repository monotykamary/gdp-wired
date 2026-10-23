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

`--backend modal` is the default again (boat's start limits proved too tight for the research volume, so boat is backup compute). `--backend auto` sends CPU work to boat and GPU work to RunPod, and Modal takes over when the
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
  start"); the plan caps them a minute, an hour and a day (`boat limits`, read at every batch, so a change of
  plan takes effect on the next batch, with no restart or setting). The hour is a rolling 60 minutes
  (`research/boat-starts/limits-log.tsv`: a start first counted at 02:41:15Z left the hour's count between 03:39:59Z
  and 03:42:01Z); the day
  didn't reset at 00:00 UTC (at 02:33Z it still counted every start since 17:00Z the day before). How a batch spends
  them (`research/boat-starts/`: today's batches replayed by `sim.py`, the defaults chosen by `tune.py` and these runs):
  - a batch starts at most a quarter of the starts left this hour and day, and at most 50 (`GDPW_BOAT_MAX_STARTS`;
    `--max-vms N` sets a run's cap, higher for an urgent run; `--vms N` asks for N outright), on top of the VMs up and
    free; it runs more jobs per VM, in its slots, longest first, rather than spending the hour;
  - the account's other users keep the last 60 starts of the rolling day and 15 of the hour
    (`GDPW_BOAT_RESERVE_DAY`, `GDPW_BOAT_RESERVE_HOUR`): this pool counts them as not there;
  - a stopped VM is resumed only while the batch still needs it (the VMs it has lack slots for what's left);
  - while a batch has more work than slots, VMs other batches release (still within their 60 s, so no start) join it,
    and once starts are back after it ran short, it asks for its share again;
  - with no start left and other batches holding VMs, `auto` waits for one they release within `--max-wait`, then
    sends the batch to Modal;
  - a released VM stays up 60 s (`--idle`) for a back-to-back batch and never longer to save starts: boat's terms
    (TOS-6) forbid parking idle compute to get around a rate limit.

  `GDPW_BOAT_POLICY=old` runs the policy before (as many VMs as speed a batch up, about sqrt(2 r W / c) at r starts a
  second, with no share, cap or waiting), to compare.
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

Starts per batch, on the $500 plan (65 starts a minute, 420 an hour, 1,680 a day), at the same commit and tree, the
old policy (`GDPW_BOAT_POLICY=old`) against the new; each figure from the run named (its `backends.json`, copied with
its summary lines to `research/boat-starts/measured/`):

| Work | Old policy | New (60 s idle, a quarter of the starts left, at most 50) | Verdicts |
| --- | --- | --- | --- |
| CHC, gdp on 1,406 tasks | 214 VMs, 211 starts, 563.7 s, $0.9588 (`runs/starts/chc-old`) | 50 VMs, 47 starts, 725.1 s, $0.33333 (`runs/starts/chc-c985479`, cap 50); 30 VMs, 30 starts, 1,116.4 s, $0.32189 (`runs/starts/chc-new`, cap 30) | no contradiction; 521 and 522 definite answers (cap 30 vs old), the rest time-limit flips (sat or unsat against unknown or timeout), as between two new runs (20 differ) |
| The suite, 204 jobs | 11 VMs, 11 starts, 245.4 s, $0.0273 (`runs/starts/suite-old`) | 5 VMs, 1 start (4 up), 429.4 s, $0.02518, with 19 starts left in the day (`runs/starts/suite-new`) | 204 exit codes the same |
| TIP, gdp on 492 | 20 VMs (`--max-vms 20`), 20 starts, 721.1 s, $0.13742 (`runs/starts/tip-old20`) | 27 VMs, 27 starts, 542.3 s, $0.13566 (`runs/starts/tip-new`) | no contradiction; 277 and 276 proven, one a timeout in the old run |

Modal's CHC (`runs/modal/arith/chc-gdp`, an earlier commit) took 330.1 s, against 725.1 s on the new policy's 50 VMs and
1,116.4 s on 30. `chc-c985479` and `suite-c985479` (8 VMs, 6 starts and 2 up, 290.8 s, $0.02485) ran with 300 s of
idle (that commit's default) and are otherwise the new policy. The simulation of today's mix (`research/boat-starts/sim.txt`, `scale.txt`, `tune-500.txt`)
has the starts a day and the walls at 1x to 4x today's volume.

A boat vCPU is faster than a Modal one (the suite's jobs in 71% of Modal's job time, 60% with `--usual`), so a fixed
limit (60 s) can let it solve more: that is the machine, not the prover. How many tasks reach the hard limit (timeout) rather than the
solver's own unknown just before it differs too: CHC 53 on boat against 8, ITS 113 against 30, TIP 136 against 177.
The batches above were sized by the plan's limits of the day ($100: 30 starts a minute, 210 an hour), so a large one
spends minutes bringing VMs up (`bring_up_s` in each `backends.json`; the TIP one counts the wait for starts too). A `large` VM (8 vCPU) ran the same eight jobs, four at a time, in 1.76
times the job time of two default VMs, two at a time (`runs/backends/large-test`): per unit of work it costs 1.7 times
as much, so the pool uses default VMs and a large one only for a job that needs 16 GB.
