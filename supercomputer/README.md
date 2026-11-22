# gdp-wired on the supercomputer: experiments in parallel

The job runner is [supercomputer](https://github.com/monotykamary/supercomputer) (`supercomputer` on the PATH): a
repo's jobs on instabox boxes, each job a detached process on its box, so a batch survives the client (a laptop
closing) and is picked up again from its output directory. `supercomputer --skill` prints its guide. This directory is
gdp-wired's side of it: the box image's setup script and the job lists; `../supercomputer.toml` says the rest (the
tree's ignore patterns, the image's PATH and environment, the `runner` image, the Lean library as a build cache).

| File | What |
| --- | --- |
| `../supercomputer.toml` | What a job here needs: instabox's `ci` template and the setup script, the box size, the toolchains first on the PATH, the tree's ignore patterns, the `runner` image (clang 18 and Temurin 17 first), the Lean twin's library as a `[[cache]]` (keyed by the toolchain and every library source), and `GDP_CYCLIC_LOG=1` before every job |
| `setup.sh` | The image: bun, Lean 4.34.0, Node 24.22.1, clang 19, JDK 21 and Temurin 17, kotlinc, Swift, Rust, solc and anvil. `supercomputer image build` runs it on a fresh box and saves the snapshot `supercomputer.toml` names |
| `suite.json` | Every runner and probe, plus the soundness fuzz as 32 seeds (`FUZZ_SEED`); also the CI shards' roster of long-suite tests (`scripts/test-shards.ts`) |
| `fuzz.json`, `one.json`, `scale.json`, `smoke.json` | The fuzz's 32 seeds alone, one seed, the grant-scale runs, the kernel's smoke runs |
| `stale_mutants.jsonl` | The mutants a past sweep left alive, each with its commit and where it changes the kernel (kernel/MUTANTS.md reads it) |

```sh
supercomputer run --jobs supercomputer/suite.json --out runs/sc/suite                        # the whole suite
supercomputer run --jobs supercomputer/suite.json --out runs/sc/usual --env GDP_CERT=usual   # the proofs' usual certificates
supercomputer batch fetch runs/sc/suite                                                      # pick a batch up again, from any checkout
supercomputer status                                                                         # the warm pool and this client's boxes
```

Results: `<out>/<name>.log` (the job's stdout and stderr), `<out>/<name>.files/` (what it wrote to
`$SUPERCOMPUTER_OUTPUT_DIR`), `<out>/summary.tsv` (name, exit or `lost`, seconds, the box it ran on) and
`<out>/batch.json`. The client exits 0 only when every job answered 0, 3 when one failed or was lost, 1 on its own
error. A job's nonzero exit is data (a failing test) and is never retried; a job whose box went away is tried again, up
to `--max-attempts` (3).

A jobs file is a list of `{"name", "cmd", "cwd"?, "cpu"?, "memory"? (MiB), "timeout"? (s), "env"?, "vm_type"?, "gpu"?,
"image"?, "distinct_vm_group"?}`; `cmd` runs under bash in `<tree>/<cwd>`, after `bun install --frozen-lockfile` where it
needs node modules (the tree ships without them). `"image": "runner"` puts a job on the `runner` image (the suite's
runner-* jobs). The tool refuses `backend`, `runtime` and `cpu_model`. `--timing` runs each job alone on a fresh box,
for a job whose seconds are compared; `--env K=V` reaches the default image's jobs (a job's own `"env"` reaches every
image).

**What changed.** gdp-wired used to run its jobs through a Python tool: boat.dev VMs first, RunPod for GPU work and
Modal as the fallback, with this directory's `run.py` (the Modal app), `hooks.py` (the boat image's layers),
`treadmill.py` (the treadmill's chains), `boat.py`, `fanout.py`, `agent.py`, `runpod.py` and `store.py` (doors to the
tool's modules) and `reap.sh`, and with each compare runner a Modal app of its own (compare/chc/modal_chc.py,
compare/term/modal_term.py, compare/tip/modal_tip.py and the rest). All of that is retired: nothing here runs on
Modal, boat or RunPod. Work that needs what those images carried (the CHC-COMP, TermComp, SV-COMP and TIP benchmarks
under /bench, /smt, /vamp and /sv, a GPU with Dawn) has no runner yet; the measurements made with them stay in their
directories' results and READMEs, and this file's earlier version (in git history) keeps the boat and Modal figures.
The old `run.py`'s `--native`, `--cyclic` and `--usual` are environment settings now: `--env GDP_LEAN_NATIVE=1`,
`--env GDP_CYCLIC=1` (with `bun test --timeout 600000` in the jobs: every proof is made twice) and
`--env GDP_CERT=usual`.

Cost hygiene: instabox bills a running box by the second and a paused one for its disk only. A batch's boxes pause into
a warm pool when it ends and the next batch resumes them; every `run` deletes paused boxes past `--keep` (30 minutes),
and `supercomputer reap --keep 30m` does it alone. A job is killed at its `timeout` (default an hour: set it per job).
Never stop a client with a broad `pkill -f`: stop it by its exact pid, and its jobs still finish on their boxes.
