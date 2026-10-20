# gdp-wired modal: experiments in parallel

| File | What |
| --- | --- |
| `run.py` | A job list fanned out on Modal, one container per job (bun and Lean 4.34.0 in the image, gdp-wired mounted fresh each run). Logs land in `<out>/<name>.log`, `summary.tsv` has exit codes and seconds |
| `suite.json` | Every runner and probe, plus the soundness fuzz as 32 seeds (`FUZZ_SEED`), about 10 minutes of wall time for over 3 hours of job time |
| (cache) | The Lean twin's library is compiled once per version of its sources: `run.py` keeps the `.olean` files on the `gdp-wired-olean` volume under a hash of every library source and the toolchain, copies them into a job before it runs and saves the ones it compiled; the suite's commands skip a library compile whose file is there (`[ -f X.olean ] ||`), except the compiles whose output a job checks |
| `reap.sh` | Stops apps whose client died (each run registers its app id and client pid in `.live/`); live runs and other apps are only listed |

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
