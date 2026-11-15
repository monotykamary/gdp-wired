# Native TLC worker (shared BAPA contract)

`research/protocols/ic3syn/tlc_native.py` exports `one(pid, ms)` and a CLI.
Run it **inside** a supercomputer native job, not on the controller:

```sh
bun install --frozen-lockfile
python3 research/protocols/ic3syn/tlc_native.py --only lock_server --ms 120000
```

Use `SUPERCOMPUTER_CONTROLLER=1 SUPERCOMPUTER_NO_BUILD=1` on the outer
`supercomputer run` command, `--backend boat`, and the repository image from
`supercomputer.toml`. The wrapper imports only Python's standard library; it
never imports Modal/supercomputer.agent, never submits a child job and derives
the repository path from `__file__`, not `/src/gdp-wired`.

One exact registry ID per job. Ports stay in `models.ts`; legacy `tlc.py` is
unchanged, and `check.ts` only adds edge-completeness reporting. Node/Bun, Python, Java/Temurin, curl and tar come from the
existing image. `--out` overrides the default `$SUPERCOMPUTER_OUTPUT_DIR`.

The worker emits the cfg using the actual `check.ts`, obtains Endive at the
existing pinned commit and TLC v1.8.0, runs the original TLA+ model, then the
positive and broken port BFS. Fixture patches come only from the repository's
TLC metadata; the two supported fixture forms are interpreted without a shell.
All commands are synchronous, individually bounded subprocesses. On timeout
or handled termination their still-owned process tree is identified through
/proc and stopped by exact PID plus birth identity, never by name/group.

`result.json` is `passed` only for complete TLC/port runs, zero positive bad
states, equal distinct states and non-stutter edges, and a demonstrably broken
negative variant. Timeout, absent graph/metadata, a nonzero exit or incomplete
BFS returns `not-verified` and worker exit 1, never a proof or protocol bug.
The broken BFS intentionally stops at a bad state; it need not explore its
entire state space. Reported BFS elapsed time must remain within `--ms`.
`check.ts` now exposes `edgeComplete=false` if its 10,000-state phase traversal
cap leaves work pending; the wrapper rejects it. No registry hook was added.
Setup projection may add port depth, so depth is reported, not compared.
Logs, actual jar SHA256, JSON metadata, generated cfg and patched root TLA+
module are retained. The temporary full graph and auxiliary TLA+ files are not.
The check compares state/edge **counts**, not their identities. TLC state fingerprints are
still TLC's probabilistic state-space evidence, not a source-equivalence theorem.

For pre-staged assets, set **both** `BAPA_TLC_ENDIVE` (directory containing
`benchmarks`) and `BAPA_TLC_JAR`. The result labels an explicit override; an
operator must bind its source identity. Otherwise the pinned cache is used.

`research/bapa/native-tlc.jobs.json` is the focused unit-control + actual
consensus smoke batch. Final batch `20261115-163827-ysb80q` passed: 7 unit
tests (including strict-negative subcases and exact child-tree termination),
real consensus TLC/port 4 states and 3 edges, positive bad=0, broken bad=3,
commitlint; native worker exit 0 in 5.48 s. Source was independently reviewed
by pi Terra (`850b9e08b9824b4e9428ca971c023066`, then
`af09a6ebb0fb49b994a10fc9dd488911`); findings were fixed. The final pidfd
acknowledgement fixes a test-observed signal-delivery/exit race.

Prior receipts remain: batch `20261115-161946-5yg1v9` had a passing initial
real smoke but its control payload never launched (agent capability ping
failure). `20261115-163124-mh603a` exposed the cleanup race; no control was
weakened and no failed attempt is relabeled as passed. It is not the 29-port regression. Each port lane should
copy the worker command into its own one-ID-per-job packet.
