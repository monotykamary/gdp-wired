// The wall corpus: laws gdp-wired proves today only when someone states what the proof needs (an invariant, a lemma
// about a recurrence or a fold), with that statement taken out. Each item's `today` is how the library proves it now;
// `frontier`, where a track has one, is the same law through that track's search, which must end in a checked proof
// of the same rule. `bun research/frontier/score.ts` runs both.
import {type Law} from '../../core/machine.ts'
import {type Verdict, fold, max, min, modBy, nat, oneOf, proveFold, proveSteps, recur, rule, when} from '../../core/dsl.ts'
import {discover, discoverFold} from '../../core/discover.ts'
import {proveLaws} from '../../kernel/prove.ts'
import {invariantCases} from '../synth/models.ts'
import {retries, retryLaws, retrySteps} from '../../examples/lemmas.ts'
import {Line, invoices, invoiceLaws, invoiceSteps} from '../../examples/invoices.ts'

export type Track = 'invariant' | 'lemma' | 'fold' | 'nonlinear' | 'structure'
export type Item = {id: string, track: Track, removed: string, today: () => Verdict, frontier?: () => Verdict}

const machineVerdict = (out: ReturnType<typeof proveLaws>): Verdict => ({proven: out.proven, checked: out.checked, ...(out.failed ? {goal: out.failed.goal, stuck: out.failed.stuck} : {})})

// Invariants: research/synth's cases, the law alone.
const invariants: Item[] = invariantCases.map(c => ({
  id: `invariant/${c.m.name}`, track: 'invariant', removed: 'the inductive invariant the law needs',
  today: () => machineVerdict(proveLaws(c.m, [c.goal])),
}))

// Recurrences with no lemma: examples/lemmas.ts's rules, each function declared again with its lemmas taken out (the
// fill meter and the tank aren't here: their law follows from the equations alone).
const twos = () => recur('twos', {zero: 0, next: (x, y) => when(x.lt(5), y.plus(2), y)}, {})
const leftovers = () => recur('leftovers', {fns: {rem: modBy(7)}, zero: 0, next: (x, l, {rem}) => l.plus(rem(x))}, {})
const growing = () => recur('growing', {zero: 1, next: (_, d) => min(d.times(2), 64)}, {})
const squares = () => recur('squares', {zero: 0, next: (x, p) => p.plus(x.times(2)).plus(1)}, {})
const lemma = (id: string, removed: string, build: () => {r: Parameters<typeof proveSteps>[0], laws: Law[]}): Item => ({
  id: `lemma/${id}`, track: 'lemma', removed, today: () => { const {r, laws} = build(); return proveSteps(r, laws, []) },
  frontier: () => { const {r, laws} = build(); return discover(r, laws).verdict },
})
const lemmas: Item[] = [
  {id: 'lemma/retry with backoff', track: 'lemma', removed: 'delay: at least 1, at most 64', today: () => { const r = retries('states no lemma'); return proveSteps(r, retryLaws(r), retrySteps(r)) },
    frontier: () => { const r = retries('states no lemma'); return discover(r, retryLaws(r), retrySteps(r)).verdict }},
  lemma('two by two', 'twos: at most 10, at most 2x', () => {
    const r = rule('two by two').inputs({}).state({n: 0, v: 0}).fns({twos: twos()}).step(({n, twos}) => ({n: n.plus(1), v: twos(n.plus(1))}))
    return {r, laws: [r.law('the value is at most 10', ({v}) => v.atMost(10))]}
  }),
  lemma('leftover ledger', 'leftovers: at most 6 a day', () => {
    const r = rule('leftover ledger').inputs({}).state({day: 0, total: 0}).fns({left: leftovers()}).step(({day, left}) => ({day: day.plus(1), total: left(day.plus(1))}))
    return {r, laws: [r.law('at most 6 a day so far', ({total, day}) => total.atMost(day.times(6)))]}
  }),
  lemma('escalation', 'growing: never shrinks (a law between two points)', () => {
    const r = rule('escalation').params({start: nat}).inputs({up: oneOf('stay', 'up')}).state({level: ({start}) => start}).fns({delay: growing()}).step(({up, level}) => ({level: when(up.is('up'), level.plus(1), level)}))
    return {r, laws: [r.law('never below the start', ({level, start}) => start.atMost(level)), r.law('the delay is at least where it started', ({level, start, delay}) => delay(start).atMost(delay(level)))]}
  }),
  lemma('area', 'squares: f(x) = x·x (a product)', () => {
    const r = rule('area').inputs({}).state({n: 0, a: 0}).fns({sq: squares()}).step(({n, sq}) => ({n: n.plus(1), a: sq(n.plus(1))}))
    return {r, laws: [r.law('the area is n·n', ({a, n}) => a.eq(n.mul(n)))]}
  }),
]

// Folds with no lemma: examples/invoices.ts's ledgers, and examples/folds.ts's org chart with its children's lemmas taken out.
const metered = () => {
  const r = rule('metered invoices').params({budget: nat, ceil: nat, fee: nat})
    .carriesList('Lines', Line, {total: {from: 0, step: (acc, l) => acc.plus(l.amount)}, charged: {from: ({fee}) => fee, step: (acc, l, {ceil}) => acc.plus(min(l.amount, ceil))}})
    .state({spent: 0, listed: 0, fees: 0})
    .flags(({Lines, budget, spent}) => ({fits: spent.plus(Lines.fold.charged).atMost(budget)}))
    .step(({Lines, fee, spent, listed, fees, fits}) => ({spent: when(fits, spent.plus(Lines.fold.charged), spent), listed: when(fits, listed.plus(Lines.fold.total), listed), fees: when(fits, fees.plus(fee), fees)}))
  return {r, laws: [r.law('nothing is spent past the budget', ({spent, budget}) => spent.atMost(budget)), r.law('what is spent is within what was listed and the fees', ({spent, listed, fees}) => spent.atMost(listed.plus(fees)))]}
}
const orgChart = () => {
  const f = fold('org chart').params({cap: nat}).inputs({pay: nat})
    .leaf(({pay, cap}) => ({cost: min(pay, cap), heads: 1, depth: 0}))
    .children({cost: 0, heads: 0, depth: 0}, (acc, kid) => ({cost: acc.cost.plus(kid.cost), heads: acc.heads.plus(kid.heads), depth: max(acc.depth, kid.depth.plus(1))}))
    .node(({pay, cap}, kids) => ({cost: kids.cost.plus(min(pay, cap)), heads: kids.heads.plus(1), depth: kids.depth}))
  return {f, laws: [f.law('the roll-up is at most the cap per head', ({cost, heads, cap}) => cost.atMost(heads.mul(cap))), f.law('a chart is at least as wide as it is deep', ({depth, heads}) => depth.lt(heads))]}
}
const folds: Item[] = [
  {id: 'fold/invoices', track: 'fold', removed: 'the taxable part is within the total, at every prefix', today: () => { const r = invoices('states no lemma'); return proveSteps(r, invoiceLaws(r), invoiceSteps(r)) },
    frontier: () => { const r = invoices('states no lemma'); return discover(r, invoiceLaws(r), invoiceSteps(r)).verdict }},
  {id: 'fold/metered invoices', track: 'fold', removed: 'the charge is within the total and the fee', today: () => { const {r, laws} = metered(); return proveSteps(r, laws, []) },
    frontier: () => { const {r, laws} = metered(); return discover(r, laws).verdict }},
  {id: 'fold/org chart', track: 'fold', removed: "the reports' lemmas: cost at most the cap per head, as many as deep", today: () => { const {f, laws} = orgChart(); return proveFold(f, laws) },
    frontier: () => { const {f, laws} = orgChart(); return discoverFold(f, laws).verdict }},
]

export const corpus: Item[] = [...invariants, ...lemmas, ...folds]
