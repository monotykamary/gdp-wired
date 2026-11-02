import {expect, test} from 'bun:test'
import {type C, type E, all, any, atMost, get, ite, n, not, plus, same, x} from './machine.ts'
import {type Count, type CountInst, checkCounted, checkMC, countHyp, countedGoal, countedOk, mcGoal} from '../kernel/kernel.ts'
import {brokenOf, clock, grow} from '../kernel/prove.ts'
import {countsForReads, proposeCountFacts, proposeCountPicks} from './count-facts.ts'
import {fixtureNames, loadFrozen, loadResidual, loadModel, recoverCounts, modelValue, pickHypsForCounts} from './fixtures/count-facts.ts'

const p = same(get('P', x('k')), n(1)), q = same(get('Q', x('k')), n(1)), r = same(get('R', x('k')), n(1))
const count = (v: string, c: C, below = x('N')): Count => ({v, key: 'k', below, body: ite(c, n(1), n(0))})
const sum = (cs: Count[], inst: CountInst): C => {
  const side = (positive: boolean): E => {
    const terms = inst.terms.filter(([c]) => positive ? c > 0 : c < 0).map(([c, v]): E => ({op: 'mul', k: Math.abs(c), a: x(v)}))
    if (positive ? inst.unit > 0 : inst.unit < 0) terms.push({op: 'mul', k: Math.abs(inst.unit), a: inst.below})
    return terms.reduce((a, b) => plus(a, b), n(0))
  }
  expect(inst.terms.every(([, v]) => cs.some(c => c.v === v))).toBe(true)
  return atMost(side(true), side(false))
}
const proveIdentity = (cs: Count[], inst: CountInst): void => {
  const g = {name: 'generated identity', counts: cs, hyps: [not(sum(cs, inst))]}
  const goal = countedGoal(g, [inst])!
  const result = grow(goal, new Map(), {nodes: 0, until: clock() + 3000})
  expect('tree' in result).toBe(true)
  if ('tree' in result) expect(checkCounted(g, {insts: [inst], tree: result.tree})).toBe(true)
}
const identityRows = (cs: Count[]) => {
  const proposed = proposeCountFacts(cs)
  return proposed.insts.filter(i => proposed.regions.some(g => g.rows.every(row =>
    i.unit + i.terms.reduce((s, [c, v]) => s + c * row[g.counts.indexOf(v)]!, 0) === 0)))
}

test('partition in both directions is proposed and checked, not assumed', () => {
  const cs = [count('whole', p), count('inside', all(p, q)), count('outside', all(p, not(q)))]
  const ids = identityRows(cs)
  expect(ids).toHaveLength(2)
  for (const i of ids) proveIdentity(cs, i)
})

test('inclusion-exclusion, complements and a three-set Venn decomposition', () => {
  const cs = [count('A', p), count('B', q), count('union', any(p, q)), count('meet', all(p, q)), count('notA', not(p))]
  const ids = identityRows(cs)
  expect(ids.length).toBeGreaterThanOrEqual(4)
  for (const i of ids) proveIdentity(cs, i)
  const regions = Array.from({length: 8}, (_, bits) => count(`region${bits}`, all(...[p, q, r].map((c, i) => bits & (1 << i) ? c : not(c)))))
  const venn = [count('A', p), ...regions]
  expect(proposeCountFacts(venn).regions[0]!.rows).toHaveLength(8)
  for (const i of identityRows(venn)) proveIdentity(venn, i)
}, 20000)

test('subset bounds are checked and majority proposes a shared-member witness', () => {
  const cs = [count('A', all(p, q)), count('B', p)]
  const out = proposeCountFacts(cs)
  const subset = out.insts.find(i => i.unit === 0 && JSON.stringify(i.terms) === JSON.stringify([[1, 'A'], [-1, 'B']]))!
  expect(subset).toBeDefined(); proveIdentity(cs, subset)
  const majority = out.insts.find(i => i.unit === -1 && i.terms.length === 2)!
  expect(majority).toBeDefined()
  const hyp = countHyp(cs, majority)!
  expect(hyp.op).toBe('or') // Not |A| + |B| <= N as an axiom!
})

test('separate bounds, nested Boolean branches, caps and unsupported bodies', () => {
  expect(identityRows([count('A', p), count('B', p, x('M'))])).toHaveLength(0)
  const cs = [count('A', p), {...count('B', p), body: ite(p, ite(q, n(1), n(1)), n(0))}]
  expect(identityRows(cs)).toHaveLength(2)
  expect(proposeCountFacts(cs, [], {maxAtoms: 0}).skipped).toHaveLength(2)
  expect(proposeCountFacts(cs, [], {maxFacts: 1}).insts).toHaveLength(1)
  expect(proposeCountFacts(cs, [], {maxFacts: NaN}).insts).toHaveLength(0)
  expect(proposeCountFacts([{...cs[0]!, body: n(2)}]).skipped[0]!.reason).toBe('non-Boolean body')
})

test('freshness includes hyps, bound keys, existing witnesses and caller reservations', () => {
  const cs = [count('region$w$0', p), count('B', p)]
  const hyps = [same(x('region$w$1'), n(0))]
  const out = proposeCountFacts(cs, [hyps, {state: {'region$w$2': 0}}], {reserved: ['region$key$0']})
  expect(countedOk(hyps, cs, out.insts)).toBe(true)
  expect(out.insts.every(i => !['region$w$0', 'region$w$1', 'region$w$2'].includes(i.wit))).toBe(true)
  expect(proposeCountFacts(cs, hyps, {reserved: ['region$w$2', 'region$key$0']})).toEqual(out)
})

test('machine reads substitute parameters in bounds and support packed keys; checker replays', () => {
  const ds = [{map: 'A', j: 'j', key: 'k', below: x('j'), body: n(1)}]
  const reads: [string, string, E][] = [['a', 'A', n(4)]]
  const cs = countsForReads(ds, reads)!
  expect(cs[0]!.below).toEqual(n(4))
  const out = proposeCountFacts(cs)
  const hyps = [not(same(get('A', n(4)), n(4)))]
  const result = grow(mcGoal(hyps, ds, {reads, insts: out.insts})!, new Map(), {nodes: 0, until: clock() + 3000})
  expect('tree' in result).toBe(true)
  if ('tree' in result) expect(checkMC(hyps, ds, {reads, insts: out.insts, tree: result.tree})).toBe(true)
  const packed = [{map: 'A', j: 'hi', lo: 'lo', base: 16, key: 'k', below: x('hi'), body: x('lo')}]
  expect(countsForReads(packed, [['a', 'A', n(4)]])).toBeUndefined()
  expect(countsForReads(packed, [['a', 'A', plus({op: 'mul', k: 16, a: n(2)}, n(3))]])![0]).toMatchObject({below: n(2), body: n(3)})
})

for (const name of fixtureNames) test(`frozen ${name}: recovered proposals resolve and are fresh`, () => {
  const raw = loadFrozen(name), cs = recoverCounts(raw.hyps)
  if (name === 'q3b-capture-7.json.gz') { expect(cs).toEqual([]); return } // flattened cells lack read definitions
  expect(cs.length).toBeGreaterThan(0)
  const out = proposeCountFacts(cs, raw)
  expect(out.insts.length).toBeGreaterThan(0)
  expect(countedOk(raw.hyps, cs, out.insts)).toBe(true)
  for (const i of out.insts) expect(countHyp(cs, i)).toBeDefined()
  // Nonnegative region populations satisfy every unconditional generated row.
  // Shared-witness rows are deliberately not asserted as unconditional facts.
  for (const i of identityRows(cs)) {
    const group = out.regions.find(g => i.terms.every(([, v]) => g.counts.includes(v)))!
    expect(group.rows.every(row => i.unit + i.terms.reduce((s, [z, v]) => s + z * row[group.counts.indexOf(v)]!, 0) === 0)).toBe(true)
  }
})

for (const name of fixtureNames) test(`frozen ${name}: count facts reject the measured spurious model`, () => {
  const raw = loadFrozen(name), saved = loadModel(name), cs = recoverCounts(raw.hyps)
  expect(brokenOf({name, hyps: raw.hyps})(saved.model)).toEqual([])
  const value = modelValue(saved.model), out = proposeCountFacts(cs, raw), picked = proposeCountPicks(cs, value)
  expect(picked.audit.filter(a => a.actual !== undefined && a.actual !== a.abstract)).toHaveLength(saved.mismatches)
  const badPicks = brokenOf({name, hyps: pickHypsForCounts(cs, picked.picks)})(saved.model)
  expect(badPicks).toHaveLength(saved.pickViolations)
  const violated = out.insts.some(i => out.regions.some(g => i.terms.every(([, v]) => g.counts.includes(v)) &&
    g.rows.every(row => i.unit + i.terms.reduce((s, [z, v]) => s + z * row[g.counts.indexOf(v)]!, 0) <= 0)) &&
    i.unit * value(i.below) + i.terms.reduce((s, [z, v]) => s + z * value(x(v)), 0) > 0)
  expect(violated || badPicks.length > 0).toBe(saved.eliminated)
})

test('concrete member picks eliminate the archived residual, not merely its current witness choices', () => {
  const raw = loadResidual(), cs = countsForReads(raw.decls, raw.reads)!
  expect(brokenOf(raw.gg)(raw.witness)).toEqual([])
  const out = proposeCountPicks(cs, modelValue(raw.witness))
  expect(out.audit.filter(a => a.actual !== a.abstract).map(a => [a.count, a.abstract, a.actual])).toEqual([
    ['r$0', 3, 5], ['r$1', 2, 4], ['r$4', 2, 4],
  ])
  expect(out.picks).toHaveLength(3)
  expect(brokenOf({name: 'picks', hyps: pickHypsForCounts(cs, out.picks)})(raw.witness)).toHaveLength(3)
})

test('picks are bounded and remain kernel-checked even with a lying evaluator', () => {
  const cs = [count('a', p, n(3))]
  const w = {a: 1, 'P[1:0]': 1, 'P[1:1]': 1, 'P[1:2]': 1}
  const out = proposeCountPicks(cs, modelValue(w))
  expect(out.picks).toEqual([['a', [n(0), n(1)]]])
  expect(proposeCountPicks(cs, modelValue(w), {maxKeys: 1}).audit[0]!.reason).toBe('pick key cap')
  expect(proposeCountPicks(cs, modelValue(w), {maxBelow: 2}).picks).toEqual([])
  const ds = [{map: 'CountP', j: 'j', key: 'k', below: n(3), body: cs[0]!.body}]
  const reads: [string, string, E][] = [['a', 'CountP', n(0)]]
  const hyps = [same(get('CountP', n(0)), n(1)), same(get('P', n(0)), n(1)), same(get('P', n(1)), n(1))]
  const cert = {reads, insts: [], picks: out.picks}
  const proof = grow(mcGoal(hyps, ds, cert)!, new Map(), {nodes: 0, until: clock() + 3000})
  expect('tree' in proof).toBe(true)
  if ('tree' in proof) {
    expect(checkMC(hyps, ds, {...cert, tree: proof.tree})).toBe(true)
    expect(checkMC(hyps, ds, {...cert, picks: [['a', [n(0), n(0)]]], tree: proof.tree})).toBe(false)
  }
  // No axioms are minted from the heuristic's numeric answer.
  const lies = proposeCountPicks(cs, e => e.op === 'const' ? e.value : e.op === 'var' ? 0 : 1)
  expect(brokenOf({name: 'real zero model', hyps: pickHypsForCounts(cs, lies.picks)})({a: 0})).toEqual([])
})

test('Q3 residual model: both partition identities hold despite concrete count mismatch', () => {
  const raw = loadResidual(), cs = countsForReads(raw.decls, raw.reads)!
  const ids = identityRows(cs)
  expect(ids.length).toBeGreaterThan(0)
  const violated = ids.filter(i => i.terms.reduce((s, [z, v]) => s + z * (raw.witness[v] ?? 0), 0) > 0 && i.unit === 0)
  expect(violated).toHaveLength(0)
  for (const i of ids) proveIdentity(cs, i)
}, 15000)
