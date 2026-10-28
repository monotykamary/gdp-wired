# NEXT (gen/protocols, checkpoint 2026-10-28)

Done:
- research/protocols/: 10 DistAI/DuoAI protocols as rules (models.ts), runner (run.ts), hand runs of 2 broken variants
  (runs.ts), README.md with sources, DuoAI Table 1 numbers, encoding, results, miss classes A-E.
- Pilot on Modal (runs/protocols/r1 in the main checkout, base = GDP_MULTI_MATCH=0 GDP_PAIRS=0 vs cand): search with
  nothing written proves 0/10 on both sides; written invariants: ticket_lock proven both, lock_server_sync and
  lock_server_async proven only with the cand's `matched` change; 2PC proven locally after a law typo fix; the rest
  unknown or killed at 420 s. Broken variants: 8 refuted with a found run, consensus_wo_decide and ring unknown (hand
  runs in runs.ts break both), sharded KV refuted locally (6 steps, 0.9 s).
- Cuts to one server (local): lock_server_sync@one proven both sides; lock_server_async@one proven only with the plain
  pair space (14 laws found; pasted back they prove it).
- Shared code: kernel/prove.ts `matched` (two reads' partial matches), core/infer.ts plain pair space (gated on a law
  about several keys), preimages reads a quantified flag as ?f, sourceOf prints pair forms as builder calls (`.n` for
  yes/no cells), core/dsl.ts `kindsOfCells()`. Library 2,387,735 -> 2,390,333 bytes (+2,598) at d8a7bbf.
- Quick bar of e83160e (before the sourceOf/kindsOfCells edits, which change no verdict) vs 3cdf37e:
  runs/bar/runs/e83160e71101-vs-3cdf37eddf65-quick-2026-10-280826/REPORT.md. CHC dev 513 vs base 517/518/517 (gained 1,
  lost 4, none solid, 3 of the 4 lost at the limit), rw dev 74 vs 74/74/73 (nothing differs), wrong 0. Estimated $1.27
  for the bar; the pilot batch (40 jobs, 5,521 s of job time) not yet read from billing.
- Local tests: infer, pairs, quantifiers, sets, steplaw, exists, sums tests pass; examples quantifiers, pairs, sets,
  infer pass.

In flight: nothing (no Modal job of this track running).

Next:
1. Read real spend (`modal billing report --for today --resolution h --json`,
   `bun gates/bar.ts spend <bar dir>`).
2. The 4 CHC losses look like limit noise (lost ones answered by the base past 45 s in 3 of 4); nested8.c is lost 2/4 vs
   6/6: check whether infer's preimages change or the pair space touches it (CHC rules have no maps, so likely the
   preimages ?f change or noise); a rerun of that one task each side locally first.
3. Add to README: the bar figures, size, reuse and spend sections; then commit (not wip).
