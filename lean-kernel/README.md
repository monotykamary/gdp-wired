# gdp-wired lean-kernel: kernel.ts checked by Lean

The optional Lean path for the kernel, as `Cert.lean` is for `core/check.ts`: a Lean 4.34.0 twin of `kernel/kernel.ts`
(its tree check, all four of its induction rules, step flags and progress laws), proven sound, and an exporter that
sends the kernel's real trees to it. `History.lean` adds kernel.ts's history rule.

| File | What |
| --- | --- |
| `Cert.lean` | A copy of `../lean/Cert.lean`: the derivation checker and `Cert.sound` |
| `Kernel.lean` | Trusted. Terms (var, const, +, ∸, × by a constant, ×, min, max, if, map reads) and conditions (≤, <, =, and, or, not) over naturals. A table names each column: a variable, a map's cell at a key over earlier columns, or a monomial (the product of earlier columns, factors sorted). `checkGoal`: path, Kleene truth, linear forms, facts, leaf rows, claimed cell equalities (re-checked), and leaf products of two rows (p ≤ 0, q ≤ 0 give −p·q ≤ 0, a pair may name an earlier product). Claimed rows are matched by coefficients, then the derivation is replayed by `Cert.check`. The induction rules build their goals in Lean, so kernel.ts's goal builders aren't trusted for them |
| `Progress.lean` | Trusted, on top of `Kernel.lean` (whose theorems it reuses unchanged). **Flags**: step terms read flag f as `.eq (.var f) (.const 1)`; `decideFlags` gives f's variable 1 when its condition holds before the step, else 0. Lean inlines flags itself (`inlineC`: the read becomes the condition, as kernel.ts's goal builder does; `inlineE`: any other read becomes `ite cond 1 0`) and proves inlining keeps the meaning. A machine with flags reaches, outside its flag variables, exactly the states its inlined machine reaches. **Progress**: Lean builds kernel.ts's two goals from the named request (the request is allowed; the step it causes makes `then` hold, primed names read the state and maps after the step) |
| `StepLaw.lean` | Trusted, on top of `Progress.lean`. **Step laws**: Lean builds kernel.ts's goal from the machine (Progress's goal with no request named: the inputs are any ι, the assumption with the flags decided is a hypothesis), so primed names read the state and maps after the step. The exporter inlines flags into `when` and `then`, which must then read no flag variable |
| `History.lean` | Trusted, on top of `Progress.lean` (reusing `fmmachine_sound` unchanged). **Histories** (kernel.ts's `historyMachine`): a machine with maps and flags plus a log of the requests it keeps (`keep`, read with the flags decided). Sums are state variables defined as the sum over the log of a term of the record (`rvars`, the recorded inputs as r.f) and the params; queries are inputs computed at each request as the sum over the log of a term of the record, the params and the plain inputs; relations (when, a, b) with `when` over params and plain inputs and a, b homogeneous over sums and queries. `HReach` is that semantics, sums recomputed from the log and queries from the log before the request. Lean builds the plain machine (`HMachine.plain`: each sum from 0, plus its term at the request when kept; relations conjoined to the assumption) and each relation's record goal (`recordGoal`: a ≤ b for one record, its fields free), and checks kernel.ts's side conditions (`histOk`) |
| `export-kernel.ts` | Untrusted. Runs `kernel/prove.ts` and writes its trees as Lean data, choosing columns (with monomials), dropping unused rows, renumbering product pairs and claiming cell pairs. Each result is a theorem by `decide +kernel`; tampered proofs appear as `example : check… = false` |
| `Trees.lean` | Everything below except the two largest machines: 356 leaves (a few repeated inside tampered records), 13 tampered proofs computed to false |
| (pruning) | Not in the Lean twin: a history's `prune` goals (a record past its order adds nothing to any query) are about the runtimes, and are checked by the TypeScript kernel only; the laws and relations Lean checks are proven over the whole history either way, so the exporters send the machine without `prune` |
| `HistoryTrees.lean` | `export-kernel.ts --history`: a sliding-window limit (`../core/models.ts`'s `windowLimit`) through `hmachine_sound`: the window ceiling, 21 leaves with the record goal's; two tampered versions computed to false |
| `TreesBig.lean` | The same plus isolation with others at other providers and the reordered admit migration, both built from admit with the grant as a flag, now passed through and inlined by Lean (`fmmachine_sound`): 878 leaves |

The theorems (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound` for each; no `sorry`, no `native_decide`):

| Theorem | Says |
| --- | --- |
| `Kern.sound` | an accepted goal's hypotheses hold for no naturals and no maps |
| `Kern.machine_sound` | scalar step machines: if `checkMachine m ps`, every law holds in every `Reach` state. `Reach.start` needs the precondition `pre`; `preOk` checks `pre` reads no input and no variable the start or a step assigns |
| `Kern.mmachine_sound` | machines with maps: one write per map per step (read-over-write as `if`), maps starting at declared constants, laws about every key proven at a fresh skolem and assumed before the step at the keys the proof names. `pre` may not read maps |
| `Kern.loop_sound` | loops: with `pre` on the params, no infinite run (`¬ ∃ f, f 0 = start ∧ ∀ n, Turn (f n) (f (n+1))`). Invariants hold at the start and each turn keeps them; a tuple of natural ranks drops lexicographically on every turn (`no_descent`: tuples of naturals of one length can't drop forever). Ranks may not read the turn's inputs |
| `Kern.inline_evalE`, `inline_evalC` | inlining flags keeps the meaning: a term or condition inlined, read in a state, equals the original read once the flags are decided (`propext` only) |
| `Kern.fmachine_sound` | scalar machines with flags (`FMachine`): if `checkFMachine f ps` (flag conditions read no flag, laws read no flag, and `checkMachine` of the inlined machine), every law holds in every `FReach` state. Via `freach_plain`: each `FReach` state agrees, outside the flag variables, with a `Reach` state of the inlined machine |
| `Kern.fmmachine_sound` | the same with maps (`FMMachine`, `FMReach`, `fmreach_plain`; writes evaluated with the flags decided) |
| `Kern.progress_sound` | progress over machines with maps and flags: if the laws' proof checks (`checkFMMachine`) and `checkProgress f ps pp` (the request names only inputs, no primed name is an input, `then` reads no flag, and both goals check), then `ProgressHolds f pp`: in every `FMReach` state where `when` holds, the named request (ι := its terms, read in that state) satisfies the assumption once the flags are decided, and `then` holds, its primed names read the state and maps after that step and its plain names the state before (with the request's inputs). `progress_reach`: the state after it is reachable too |
| `Kern.steplaw_sound` | step laws over machines with maps and flags: if the laws' proof checks (`checkFMMachine`) and `checkStepLaw f ps sl` (`when` and `then` read no flag, and the goal checks), then `StepLawHolds f sl`: in every `FMReach` state, every request (inputs ι) that satisfies the assumption once the flags are decided and that `when` admits takes a step where `then` holds, primed names reading the state and maps after it. A history machine's step laws go through its plain machine (`historyMachine`) |
| `Kern.hmachine_sound` | machines with a history (`HMachine`): if `checkHMachine h ps rs` (`histOk`, a checked record goal per relation, and `checkFMMachine` of the plain machine), every law holds in every `HReach` state, sums read as their sums over the log. Via `hreach_fmreach`: every `HReach` state is an `FMReach` state of the plain machine, the relations holding of each request because they hold of each record (`homog_sum`: a homogeneous term over sums of one list is the sum of the term; `sum_le_map`) |
| `Kern.fold_sound` | folds over binary trees with inputs at leaves and nodes: every law holds of every tree whose inputs meet `assume` (leaf goal, and node goal from both children through per-side copies of the state) |

Exported through those rules, with plain-Lean corollaries:

| Export | Rule | Corollary |
| --- | --- | --- |
| budget rule, in-flight | `machine_sound` | `bounded_loss : ρ 3 ≤ ρ 0 + ρ 1`, `inflight_loss` |
| s ≤ m × requests (grind's lemma, a product) | `machine_sound` | `loss_per_request : ρ 2 ≤ ρ 0 * ρ 3` |
| the caps rule's 4 caps, per-account isolation (big: isolation at other providers, the reordered migration) | `mmachine_sound` | `day_cap : M 1 k ≤ ρ 0` for every key k |
| gcd (pre A, B ≥ 1), pagination, retry, the grid walk with ranks (n ∸ i, m ∸ j) | `loop_sound` | `gcd_halts`, `grid_halts`, … |
| a sliding-window limit: window_ceiling, with `ours` (admitted requests in the window ending at now) a sum over the log and `seen` (the requests logged within w before the request) a query, and the relation at t ≤ now, ours ≤ seen | `hmachine_sound` | `window_ceiling : ρ 6 ≤ ρ 1` (ours ≤ c) in every reachable state |
| tree shape (3 laws), spend roll-up with cap 50 and with cap m (a product) | `fold_sound` | `leaves_eq_nodes_succ : leaves = nodes + 1` for every tree |
| x ≤ x·x (products of rows) and the policy/in-flight goals | `sound` | |
| budget rule with its guard as a flag (room := s < b) | `fmachine_sound` | `fpolicy_laws` |
| caps rule with the grant as a flag (4 caps); big: isolation and the reordered migration, both from the flagged admit | `fmmachine_sound` | `fadmit_laws`, `iso_laws`, `migration_laws` |
| run-progress.ts: a request in flight can always complete (3 leaves), under budget with room one is admitted (4); an account under every cap gets its grant (6), also with the grant as a flag (6) | `progress_sound` | `flight_complete_holds`, `flight_admit_holds`, `admit_grant_holds`, `fadmit_grant_holds` |

Tampered, each computed to false: the policy proof on the uncapped machine; gcd without its precondition; pagination
when a page may be empty; the roll-up proof with leaves capped at 51; the admit proof with the Day cap unguarded; an
emptied leaf; the window proof offered for the relation claimed at every t (its record goal fails) and for the relation left out (the ceiling's step goal fails); the bounded_loss tree offered for s ≤ b; the x ≤ x·x tree offered for x·x ≤ x; and a loop whose rank reads
the turn's input (`forever`, below); the flagged policy proof on a flag that always admits; the flagged admit proof on
a grant flag without the Day cap; the in-flight completion proof offered for "with none in flight, one completes"; and
the grant proof offered for "even with the day full". The last two are run-progress.ts's false variants.

**kernel.ts gap found here, since fixed:** `loopObligations` accepted ranks that read the turn's inputs. `forever`
(state x from 0, input w, while x < w, x := x + 1, rank w ∸ x) passed kernel.ts's check, yet the loop runs forever when
every turn sends w = x + 1. kernel.ts now refuses such ranks; the exporter writes `forever`'s rank goal out by hand, it
still checks on its own in Lean (shown in `Trees.lean`), and `checkLoop` rejects it because the rank mentions an input.

```sh
TC=~/.elan/toolchains/leanprover--lean4---v4.34.0; export LEAN_PATH=$PWD:$TC/lib/lean
$TC/bin/lean -o Cert.olean Cert.lean && $TC/bin/lean -o Kernel.olean Kernel.lean   # 8–17 s
$TC/bin/lean -o Progress.olean Progress.lean                                        # ~3 s
bun export-kernel.ts > Trees.lean && $TC/bin/lean Trees.lean                       # 13 s on the Mac, 19 s on Modal (4 CPUs)
bun export-kernel.ts --big > TreesBig.lean && $TC/bin/lean TreesBig.lean           # 40 s on Modal (4 CPUs)
$TC/bin/lean -o StepLaw.olean StepLaw.lean                                          # ~10 s on Modal
$TC/bin/lean -o History.olean History.lean                                          # ~8 s on the Mac
bun export-kernel.ts --history > HistoryTrees.lean && $TC/bin/lean HistoryTrees.lean # ~13 s on the Mac
```

On Modal (`../runs/lean-progress-jobs.json`, logs in `../runs/modal/lean-progress/`) both files checked with no
errors, every exported theorem on `propext`, `Classical.choice`, `Quot.sound`.

Not covered by the twin:
- **Flags inside `then`** of a progress law: kernel.ts allows them (read at the request), `checkProgress` refuses them.
  Flags inside a flag's condition are refused by both.
- **Progress over scalar `Machine`s** goes through `FMMachine` with no maps (in-flight is exported that way).
- **The `natural` check** has no counterpart because Lean's terms are natural by construction (constants and factors
  are `Nat`).
- **Histories**: Lean's log holds whole request environments; sums and queries read only the recorded inputs from them
  (through `fieldSub`), as kernel.ts's records hold only those. `histOk` also asks that the precondition read no input,
  flag or field and no map, which kernel.ts's `preOf` already implies for every machine.
- Lean is stricter than kernel.ts in places, never looser: a law may not read a flag, a progress request's keys must be
  inputs and primed names may not be, a product pair that fails to
  multiply rejects the leaf (kernel.ts adds an empty row), and a monomial column must be present for every product
  of two columns a row needs.
