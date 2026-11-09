# Lane E — guarded inclusion integration (in progress)

Branch: `claude/mldr-incl`. This section supersedes the old assignment below.
**NOT GATE GREEN; not a merge candidate yet.**

Source commits: **`f6ec83db`** (ordinary preference) and **`7dc52140`**
(raw-pool admission and shared-cap correction).

The existing generic member matcher now reaches `rawBuild`'s ordinary lazy
pool through `grammarPool`. New entries use the pool's existing semantic dedup,
fresh-witness allocation, cap and proposal meter. Initial selection can prefer
those entries while sharing the ten-slot bound with picks. No scalar residue is
asserted: each entry is the ordinary count-witness disjunction, and source
branches and the final certificate still pass the unchanged kernel.

Checks on boat (`runs/mldr-incl-check-v1/`): `bun run check` passed and the four
focused test files passed **86 tests, zero failures**. New tests cover bounded
selection, reuse of the exact existing witness, immutable inputs, missing source
flags, and refusal to manufacture a missing pool instance.

Unchanged-source original MLDR baseline (`runs/mldr-incl-baseline-v1/`): three
strict 60 s trials returned UNKNOWN; job times were 59.59, 59.61, and 59.57 s.
The production-query capture (`runs/mldr-incl-capture-v1/`) also returned UNKNOWN,
ending amid generated stored-guard helper attempts. The full query ledger has
794 rows. The bounded archive retained 142 files and omitted 752; it must not be
represented as a complete archive of every raw stage.

The 24-job conditional matrices v1/v2 did not produce a complete receipt and
were stopped by exact owned task ID after scheduler turnover/stalls. They are
not acceptance evidence. The current v3 batch has only the baseline/preferred
2,700-unit safety captures and a 55 KiB input instead of the unnecessary 51 MiB
stage archive. All remain **conditional one-law diagnostics**, not complete
family proofs. The optional 5,000-unit matrix points are above the target share.

Later validation (`mldr-incl-check-v3` through `v5`) exposed one replay-harness
type error and two incorrect expectations in a synthetic bound/cap test. The
harness type error is fixed; type/lint passed in v4/v5. The test now checks the
new bound-specialized instance independently of invalid legacy tuples and tests
refusal with an actually full one-entry cap. In `mldr-incl-members-v6`, the new
generic conditional proof passed `checkMC`, and its unguarded strengthening was
not proved. That run had **15 passes / 1 cap-expectation failure**; the corrected
16-test rerun is pending, not claimed green.

**Infrastructure block:** boat refused the E-14 capture submission with
`recovery quarantined; ownership held`. Controller status reported no controller
VM. No ownership guard or shared policy was bypassed; no other client's VMs were
touched. The corrected member regression and two conditional captures remain
owned pending jobs; IDs and next steps are in `research/mldr-incl/WORKING.md`.

Lane A's E-14 is now available as `1681e8e5`. A generation-only capture in an
isolated checkout is prepared, with zero proof queries asserted and no hand law.
Its first submission was refused before execution. Lane B's key completion is
available as `60b8c37a`; no counterpart changes were silently imported into this
lane. No MLDR proof improvement, integrated sub-60 s result, or gate pass is
claimed.

Required before a merge claim: checked conditional safety improvement; replay on
E-14's actual output; strict original MLDR confirmation; paired IC3Syn 29x3 versus
main, DuoAI, broken variants, bar, type/lint and tests. No merge or push performed.
