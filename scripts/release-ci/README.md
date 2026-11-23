# Release CI

- [FULL-GATE.md](./FULL-GATE.md): the release's full gate, every job of `supercomputer/suite.json` run once at the
  release commit as one strict-once supercomputer batch on instabox, from `publish.yml` (`full-suite.ts`), and the
  failures it accepts (`known-failures.json`, `known-failures.ts`, bound to each job's definition by `job-hash.ts`).
- `KEYED-SECTION-EVIDENCE.md`, `known-failures-keyed-evidence.json`: the evidence behind the keyed Lean known failure.
- `python-litellm-regression.sh`, `agent-consult-packed.sh` (with `agent-consult-packed-fixture.mjs`): suite jobs' own
  scripts.

The historical 0.48.0 boat-era control helpers (local preparation, supplemental receipt checks, negative controls,
the control-tree hook adapter) are retired with boat; they are in git history.
