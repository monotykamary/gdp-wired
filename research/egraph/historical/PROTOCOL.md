# Historical comparison protocol (preliminary diagnostics)

Accepted e-graph source: `662a1c07e4a521b04a2f05bfc4275d9660eb8ca0`, tree
`922525a6db74c1092f8ae9c8109930a3ccfad246`; implementation `cfa11fc7`.
Canonical M2 baseline: `444ece6ebe42d202150bc583c0c55b626b4e32c9`, tree
`517d8462ade04456254dc6db0e6132cc4bae94ce`. Its complete immutable export lives
in ignored `runs/astra-history-baselines/m2-444`, never in the old worktrees.
The Q3/RL branch tips at pause both name `9753cce0d637df0618cd2a61650ea104a916ea7c`;
that is NOT a substitute for the M2 engine pin. Archived uncommitted state is
not silently relabeled as a Git commit.

## Acceptance ledger

1. Verify the archive manifest before requesting lane members. Read Q3 and RL
   NEXT/checkpoints, locate exact saved fixture IDs, hashes and original settings.
2. Reproduce Paxos full published-context outcomes on the canonical M2 engine:
   open `one value decided` and `P3 decision has quorum`; retain P1/P2/P4/P5 positives.
   Each focus is first in the same full context; `search:false`, 25,000 ms outer
   cooperative prover ceiling. A saved model is a separate diagnostic, not a flip.
3. Compare accepted matcher enabled/disabled on IDENTICAL engine/kernel, input,
   assumptions and budgets. Keep unsupported `if`, `flag`, `all`, missing bridge,
   cap exhaustion and missing proof outcomes explicit. Do not project an unsupported
   whole goal into a convenient synthetic theorem.
4. TIP: use the archived theorem text, translator settings and genuine independently
   proved reverse/append lemma. Count checked reachable lemma uses on the exact full
   theorem, not a new recursive-tail surrogate. Keep removal/corruption controls.
5. Recheck every returned cyclic node, premise, descent and both split branches with
   the unchanged kernel. Split hints, if used, are explicitly supplied, not extracted.
6. Bind source/input/proof hashes before and after. Preserve every failed run and
   worker exit (controller exit alone is insufficient). Request 2 CPU/4096 MiB/600 s,
   one active job at a time. Runs are untimed correctness diagnostics, never speedups;
   cooperative budgets do not establish hard CPU/RAM bounds.
7. Final end-to-end acceptance requires Sol's validated native producer/admission and
   full-gate evidence. Until then every result is preliminary; no merge/push permitted.

## Preservation

`archive-meta/store-manifest.json` binds all eight archive members. Only Q3 and RL
archives are streamed into temporary files on boat. No archive path is extracted
into historical worktrees. The first metadata request returned an HTTP redirect;
`runs/astra-history-archive-meta/failed-redirect.html` is retained outside Git because the redirect contains the expired private store path. Initial archive index was overly broad and missed
root `NEXT.md`; its original runner/log remains, and v2 corrects only selection.
