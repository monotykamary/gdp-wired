// The termination items: TermComp's integer transition systems (TPDB-ARI at 183f29d) and SV-COMP's termination tasks
// (sv-benchmarks at c5cc603, the C program translated by compare/term/c2ari.py, as the benchmark run did) that another
// tool proves terminating and gdp-wired doesn't (runs/backends/term-gdp, runs/modal/term/sv3). Each is the task as
// compare/term/translate.ts reads it: one loop over every location, its runs the task's runs from any integers, so the
// loop halts from every start exactly when the task terminates (the task's own statement, not the per-component one of
// scc.ts). `today` is round 1's loop templates (kernel/run-more.ts's: a state variable, a param minus a state variable, a
// sum of two state variables, each checked by the kernel); `frontier` is proveLoop's search as compare/term/solve.ts runs
// it (core/cycles.ts's findRank within the benchmark's 60 s less solve.ts's 9 s margin), its goals checked again by the
// kernel on the loop as translated. A broken variant is the task changed so that some run never ends (LoAT answers NO:
// research/frontier2/truth-term.json), which nothing may prove halts.
import {readFileSync} from 'node:fs'
import type {E} from '../../core/machine.ts'
import type {Verdict} from '../../core/dsl.ts'
import {type Loop, check, loopObligations} from '../../kernel/kernel.ts'
import {grow} from '../../kernel/prove.ts'
import {findRank, showE} from '../../core/cycles.ts'
import {parseAri} from '../../compare/term/ari.ts'
import {build} from '../../compare/term/translate.ts'
import type {Item, Source, Track} from './corpus.ts'

const loopOf = (file: string): Loop => build(parseAri(readFileSync(`${import.meta.dir}/tasks/${file}`, 'utf8')), file.split('/').pop()!).loop
const v = (name: string): E => ({op: 'var', name})

// Round 1's templates (research/frontier/cycles.ts), each rank checked by the kernel.
function templates(l: Loop): Verdict {
  const st = Object.keys(l.state), sub = (a: E, b: E): E => ({op: 'sub', a, b}), add = (a: E, b: E): E => ({op: 'add', a, b})
  const ranks: E[] = [...st.map(v), ...l.params.flatMap(p => st.map(s => sub(v(p), v(s)))), ...st.flatMap((s, i) => st.slice(i + 1).map(w => add(v(s), v(w))))]
  for (const r of ranks) {
    if (loopObligations(l, [], r).every(g => { const o = grow(g); return 'tree' in o && check(g, o.tree) })) return {proven: true, checked: true, found: {rank: showE(r)}}
  }
  return {proven: false, checked: false, why: `no rank among ${ranks.length} templates`}
}
// findRank as solve.ts runs it, then every halting goal's tree checked again on the loop as translated.
function searched(l: Loop): Verdict {
  const f = findRank(l, [], {ms: 51_000})
  if (f.proven && f.checked && f.rank && f.trees) {
    const goals = loopObligations(l, f.laws ?? [], f.rank)
    const missing = goals.filter(g => !f.trees![g.name] || !check(g, f.trees![g.name]!)).map(g => g.name)
    if (!missing.length) return {proven: true, checked: true, found: {rank: `(${f.rank.map(showE).join(', ')})`, ...(f.found?.laws.length ? {facts: f.found.laws} : {})}}
    return {proven: false, checked: false, why: `the kernel refused a tree on the recheck: ${missing.join(', ')}`}
  }
  return {proven: false, checked: false, ...(f.goal ? {goal: f.goal, stuck: f.stuck} : {}), why: f.why ?? 'no rank'}
}

type Spec = {task: string, file: string, track: Track, removed: string, group: string, truth: string, broken: {file: string, what: string, truth: string}[]}
const its = 'TermComp ITS' as const, sv = 'SV-COMP termination' as const
const specs: (Spec & {benchmark: Source['benchmark']})[] = [
  {benchmark: its, task: 'Integer_Transition_Systems/From_AProVE_2014/Continue1.jar-obl-8.ari', file: 'its/Continue1.jar-obl-8.ari', track: 'rank',
    removed: 'a rank that reads no param: 20 − x (x := 0; while x < 20: x := x + 1, two rules split at 10)', group: 'a rank fitted to the params',
    truth: 'KoAT2 Finite, MPRFs 20 − X₀ and 21 − X₀; LoAT abmc YES (runs/corpus2/truth-term)', broken: [{file: 'its/Continue1.jar-obl-8.broken.ari', what: 'the bound x < 20 dropped from the rule for x > 9', truth: 'LoAT NO, LoAT abmc NO (runs/corpus2/truth-term)'}]},
  {benchmark: its, task: 'Integer_Transition_Systems/From_T2/p-60.t2_fixed.ari', file: 'its/p-60.t2_fixed.ari', track: 'rank',
    removed: 'a rank that reads no param: 101 − i (while i <= 100 and x >= 1: i := i + 1; three slots nothing reads)', group: 'a rank fitted to the params',
    truth: 'KoAT2 Finite, MPRFs 101 − X₀ and 102 − X₀; LoAT abmc YES (runs/corpus2/truth-term)', broken: [{file: 'its/p-60.t2_fixed.broken.ari', what: 'the bound i <= 100 dropped from the loop\'s rule', truth: 'LoAT NO, LoAT abmc NO (runs/corpus2/truth-term)'}]},
  {benchmark: its, task: 'Integer_Transition_Systems/From_AProVE_2014/AckR.jar-obl-8.ari', file: 'its/AckR.jar-obl-8.ari', track: 'rank',
    removed: 'the lexicographic rank (y, x), tried after the linear one the runs fit is refused (an iterative Ackermann: at x = 0, x := 1 and y := y − 1; at x > 0, x := x − 1, or x := any v >= 1 and y := y − 1)', group: 'a rank the kernel refused, no param read',
    truth: 'KoAT2 Finite, MPRFs 1 + X₁ on the two rules that lower y and 1 + X₀ + X₁ on the one that lowers x (LoAT no answer in 70 s) (runs/corpus2/truth-term)', broken: [{file: 'its/AckR.jar-obl-8.broken.ari', what: 'x := x − 1 made x := x', truth: 'LoAT NO, LoAT abmc NO (runs/corpus2/truth-term); a lasso (stem 3, cycle 1) confirmed by compare/term/ari.ts\'s checkLasso (runs/corpus2/truth-term-lassos)'}]},
  {benchmark: its, task: 'Integer_Transition_Systems/From_AProVE_2014/Alternate.jar-obl-10.ari', file: 'its/Alternate.jar-obl-10.ari', track: 'rank',
    removed: 'a rank per location: three loops of two locations each after chaining, each with its own rank (x1 + x2, x0 + x2 − 2, ...)', group: 'a rank the kernel refused, no param read',
    truth: 'KoAT2 Finite, an MPRF per location (X₀ + X₂ − 2, 1 + X₂ + X₃, X₀ at copy\'s, ...) (LoAT no answer in 70 s) (runs/corpus2/truth-term)', broken: [{file: 'its/Alternate.jar-obl-10.broken.ari', what: 'the copy loop\'s x\' + 1 <= x made x\' <= x', truth: 'LoAT NO, LoAT abmc NO (runs/corpus2/truth-term)'}]},
  {benchmark: its, task: 'Integer_Transition_Systems/Britikov_26/toy3.t2.ari', file: 'its/toy3.t2.ari', track: 'rank',
    removed: 'a rank in phases: 100 − x until x >= 100, then y\'s sign (y, −y) (x := 0; while y > 1 or y < 0: x := x + 1, and y := 0 once x >= 100)', group: 'a rank the kernel refused, no param read',
    truth: 'KoAT2 Finite, MPRFs 100 − X₀, X₁ and −X₁; LoAT abmc YES (runs/corpus2/truth-term)', broken: [{file: 'its/toy3.t2.broken.ari', what: 'y := 0 at x >= 100 made y := y', truth: 'LoAT NO, LoAT abmc NO (runs/corpus2/truth-term)'}]},
  {benchmark: its, task: 'Integer_Transition_Systems/From_T2/polyrank1.t2.ari', file: 'its/polyrank1.t2.ari', track: 'nonlinear rank',
    removed: 'a multiphase rank: y climbs until it is positive, then x drops (while x >= 1: x := x − y; y := y + 1)', group: 'a rank fitted to the params',
    truth: 'the multiphase rank (1 − y, x), each of its three conditions checked by z3 (tasks/its/polyrank1.t2.rank.smt2: three unsat, runs/corpus2/truth-polyrank1); LoAT abmc YES, KoAT2 no claim, LoAT MAYBE (runs/corpus2/truth-term)', broken: [{file: 'its/polyrank1.t2.broken.ari', what: 'y := y + 1 made y := y − 1', truth: 'LoAT NO, LoAT abmc NO (runs/corpus2/truth-term)'}]},
  {benchmark: sv, task: 'termination-crafted/2Nested-1.yml', file: 'sv/2Nested-1.ari', track: 'nonlinear rank',
    removed: 'a 2-nested (multiphase) rank: y + 1, then x (while x >= 0: x := x + y; y := y − 1, x and y bounded by 65534 first)', group: 'a rank fitted to the params',
    truth: 'SV-COMP\'s expected verdict true (termination.prp); LoAT abmc YES (runs/corpus2/truth-term; KoAT2 no claim); Ultimate Automizer YES on the C program (runs/modal/term/sv2)', broken: [{file: 'sv/2Nested-1.broken.ari', what: 'y = y − 1 made y = y + 1 (in the C program, then c2ari.py)', truth: 'LoAT NO, LoAT abmc NO (runs/corpus2/truth-term)'}]},
  {benchmark: sv, task: 'termination-crafted/Toulouse-BranchesToLoop-2.yml', file: 'sv/Toulouse-BranchesToLoop-2.ari', track: 'nonlinear rank',
    removed: 'a rank by x\'s sign: 100 − y where x = 1, 100 − z where x = −1 (two products with x, or a guard in the rank) (x := 1 or −1; while y < 100 and z < 100: y := y + x; z := z − x)', group: 'no rank fits the sampled turns',
    truth: 'SV-COMP\'s expected verdict true; LoAT abmc YES (runs/corpus2/truth-term; KoAT2 no claim); Ultimate Automizer YES (runs/modal/term/sv2)', broken: [{file: 'sv/Toulouse-BranchesToLoop-2.broken.ari', what: 'x = −1 made x = 0', truth: 'LoAT NO (runs/corpus2/truth-term); a lasso (stem 14, cycle 4) confirmed by checkLasso (runs/corpus2/truth-term-lassos); LoAT abmc answered YES on it, which the lasso contradicts'}]},
  {benchmark: sv, task: 'termination-crafted/Piecewise.yml', file: 'sv/Piecewise.ari', track: 'nonlinear rank',
    removed: 'the rank min(p, q) (while q > 0 and p > 0 and p != q: if q < p: q := q − 1, p := any; else if p < q: p := p − 1, q := any)', group: 'a rank the kernel refused, no param read',
    truth: 'SV-COMP\'s expected verdict true; Ultimate Automizer YES (runs/modal/term/sv2); here LoAT MAYBE, LoAT abmc no answer in 70 s, KoAT2 an internal error (runs/corpus2/truth-term)', broken: [{file: 'sv/Piecewise.broken.ari', what: 'q = q − 1 made q = q', truth: 'LoAT NO, LoAT abmc NO (runs/corpus2/truth-term); a lasso (stem 6, cycle 6) confirmed by checkLasso (runs/corpus2/truth-term-lassos)'}]},
  {benchmark: sv, task: 'termination-crafted/McCarthy91_Iteration.yml', file: 'sv/McCarthy91_Iteration.ari', track: 'nested recursion',
    removed: 'McCarthy\'s nested recursion as a loop with its depth c: a rank that needs the region n <= 111 as an invariant (c := 1; while c > 0: if n > 100: n := n − 10, c := c − 1 else n := n + 11, c := c + 1)', group: 'a rank the kernel refused, no param read',
    truth: 'SV-COMP\'s expected verdict true; KoAT2 Finite (runs/corpus2/truth-term); Ultimate Automizer YES (runs/modal/term/sv2)', broken: [{file: 'sv/McCarthy91_Iteration.broken.ari', what: 'c = c − 1 made c = c', truth: 'LoAT abmc NO (LoAT MAYBE) (runs/corpus2/truth-term)'}]},
  {benchmark: its, task: 'Integer_Transition_Systems/From_AProVE_2014/AProVEMath.jar-obl-8.ari', file: 'its/AProVEMath.jar-obl-8.ari', track: 'sampling',
    removed: 'runs whose inputs meet an equation (x = 2·q for a fresh q), so the halving loop takes a turn; then rank x (while x > 0: x := x\' with 0 <= x − 2·x\' < 2)', group: 'no turn sampled (an input pinned by an equation)',
    truth: 'KoAT2 Finite, MPRFs 1 + X₀, 2·X₀ − 1 and X₀ (LoAT MAYBE) (runs/corpus2/truth-term)', broken: [{file: 'its/AProVEMath.jar-obl-8.broken.ari', what: 'the even case\'s halving made x\' = x', truth: 'LoAT NO, LoAT abmc NO (runs/corpus2/truth-term); a lasso (stem 3, cycle 2) confirmed by checkLasso (runs/corpus2/truth-term-lassos)'}]},
  {benchmark: its, task: 'Integer_Transition_Systems/From_AProVE_2014/ListReverseCyclicList.jar-obl-10.ari', file: 'its/ListReverseCyclicList.jar-obl-10.ari', track: 'sampling',
    removed: 'runs that meet several bounds on fresh values at once (a list built, then reversed; each turn\'s values fresh, bounded by the old)', group: 'no turn sampled (several nondeterministic values bounded together)',
    truth: 'KoAT2 Finite, an MPRF per location (3 + X₂ at createList\'s, 1 + X₁, X₃, ...) (LoAT MAYBE) (runs/corpus2/truth-term)', broken: [{file: 'its/ListReverseCyclicList.jar-obl-10.broken.ari', what: 'the list builder\'s counter n := n − 1 made n := n', truth: 'LoAT NO, LoAT abmc NO (runs/corpus2/truth-term)'}]},
  {benchmark: sv, task: 'termination-crafted/WhileFalse.yml', file: 'sv/WhileFalse.ari', track: 'sampling',
    removed: 'any rank where the loop takes no turn (while false: skip); with no turn sampled no rank is tried', group: 'no turn sampled',
    truth: 'SV-COMP\'s expected verdict true; KoAT2 Finite, LoAT abmc YES (runs/corpus2/truth-term)', broken: [{file: 'sv/WhileFalse.broken.ari', what: 'while (false) made while (true)', truth: 'LoAT NO, LoAT abmc NO (runs/corpus2/truth-term); a lasso (stem 2, cycle 2) confirmed by checkLasso (runs/corpus2/truth-term-lassos)'}]},
]

const id = (s: Spec) => `term/${s.task.split('/').pop()!.replace(/\.(ari|yml)$/, '')}`
export const termItems: Item[] = specs.flatMap(s => [
  {id: id(s), track: s.track, removed: s.removed, source: {benchmark: s.benchmark, task: s.task, group: s.group}, truth: s.truth,
    today: () => templates(loopOf(s.file)), frontier: () => searched(loopOf(s.file))},
  ...s.broken.map((b): Item => ({id: `${id(s)} (broken: ${b.what})`, track: s.track, removed: s.removed, broken: id(s), source: {benchmark: s.benchmark, task: s.task, group: s.group}, truth: b.truth,
    today: () => templates(loopOf(b.file)), frontier: () => searched(loopOf(b.file))})),
])
