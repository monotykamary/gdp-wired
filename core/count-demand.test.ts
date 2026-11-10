import {expect, test} from 'bun:test'
import {type C, all, get, ite, less, n, not, plus, same, x} from './machine.ts'
import {type Count, type CountInst, checkCounted, countHyp, countedGoal, countedOk} from '../kernel/kernel.ts'
import {clock, grow} from '../kernel/prove.ts'
import {proposeCountDemand} from './count-demand.ts'
import {proposeCountUnions} from './count-unions.ts'

const bit = (c: C) => ite(c, n(1), n(0))
const count = (v: string, body: Count['body'], key = 'member', below = n(4)): Count => ({v, body, key, below})
const at = (map: string, key = 'member') => get(map, x(key))
const member = (map: string, key = 'member') => same(at(map, key), n(1))
const termsKey = (terms: [number, string][]) => JSON.stringify([...terms].sort((a, b) => a[1].localeCompare(b[1])))
const signature = (i: CountInst) => termsKey(i.terms)
const sum = (names: string[]) => names.reduce((a, name) => plus(a, x(name)), n(0))

function family(prefix: string): Count[] {
  const a = member(`${prefix}A`), b = member(`${prefix}B`)
  return [count(`${prefix}left`, bit(all(a, not(b)))), count(`${prefix}both`, bit(all(a, b))), count(`${prefix}right`, bit(all(not(a), b)))]
}
function problem(prefix = ''): Count[] {
  const a = member(`${prefix}A`), b = member(`${prefix}B`), v = member(`${prefix}V`)
  return [count(`${prefix}remaining`, bit(all(a, not(v)))), count(`${prefix}selected`, bit(all(b, v))), ...family(prefix)]
}
const target = (prefix = '') => termsKey([[1, `${prefix}remaining`], [1, `${prefix}selected`], [-1, `${prefix}left`], [-1, `${prefix}both`], [-1, `${prefix}right`]])

function prove(counts: Count[], inst: CountInst, hyps: C[]): void {
  const g = {name: 'synthetic demand proposal', counts, hyps}
  expect(countedOk(hyps, counts, [inst])).toBe(true)
  const goal = countedGoal(g, [inst])!
  const proof = grow(goal, new Map(), {nodes: 0, until: clock() + 2000})
  expect('tree' in proof).toBe(true)
  if ('tree' in proof) expect(checkCounted(g, {insts: [inst], tree: proof.tree})).toBe(true)
}

test('one-fact pair requests do not regenerate a partition prefix', () => {
  const counts = [...problem(), count('wholeA', bit(member('A')))]
  const out = proposeCountDemand(counts, new Set(['remaining', 'selected', 'wholeA']), {
    pairs: [['remaining', 'selected']], partitions: false, maxFacts: 1,
  })
  expect(out).toHaveLength(1)
  expect(signature(out[0]!)).toBe(target())
})
test('demand reaches a relevant family beyond 128 irrelevant legacy proposals', () => {
  const noise = Array.from({length: 9}, (_, i) => [count(`noise${i}x`, at(`NX${i}`)), count(`noise${i}y`, at(`NY${i}`))]).flat()
  const unrelated = Array.from({length: 15}, (_, i) => family(`unrelated${i}`)).flat()
  const counts = [...noise, ...unrelated, ...problem()]
  const pairs: [string, string][] = Array.from({length: 9}, (_, i) => [`noise${i}x`, `noise${i}y`])
  pairs.push(['remaining', 'selected'])
  // This is a regression fixture for the old eager pool, not the new algorithm.
  const legacy = proposeCountUnions(counts, pairs, 4096)
  expect(legacy.findIndex(i => signature(i) === target())).toBeGreaterThanOrEqual(128)
  const demand = new Set(['remaining', 'selected'])
  const insts = proposeCountDemand(counts, demand, {pairs})
  expect(insts.length).toBeGreaterThan(0)
  expect(insts.length).toBeLessThanOrEqual(128)
  expect(insts.some(i => signature(i) === target())).toBe(true)
  expect(insts.flatMap(i => i.terms.map(([, id]) => id)).every(id => problem().some(c => c.v === id))).toBe(true)
  // Goal-read mode needs no caller-generated pair pool at all.
  expect(proposeCountDemand(counts, demand).some(i => signature(i) === target())).toBe(true)
})

test('late counts are indexed, not clipped to the first 128 inputs', () => {
  const counts = [...Array.from({length: 50}, (_, i) => family(`noise${i}`)).flat(), ...problem()]
  const insts = proposeCountDemand(counts, new Set(['remaining']), {pairs: [['remaining', 'selected']]})
  expect(insts.map(signature)).toEqual([target()])
})

test('one demanded count finds an undemanded carried partner in a generic 41-read shape', () => {
  const [remaining, , ...regions] = problem()
  const counts = [remaining!, ...regions, ...Array.from({length: 12}, (_, i) => family(`unused${i}`)).flat(), count('selected', at('Carried'))]
  expect(counts).toHaveLength(41)
  const insts = proposeCountDemand(counts, new Set(['remaining']))
  expect(insts.length).toBeLessThanOrEqual(128)
  expect(insts.map(signature)).toContain(target())
  expect(signature(insts[0]!)).toBe(target())
  expect(insts.flatMap(i => i.terms).some(([, id]) => id.startsWith('unused'))).toBe(false)
})

test('positive pairs require a demanded endpoint and a same-bound relevant family', () => {
  const counts = [...problem(), ...problem('other')]
  const options = {pairs: [['otherremaining', 'otherselected']] as const}
  expect(proposeCountDemand(counts, new Set(['remaining']), options)).toEqual([])
  expect(proposeCountDemand(counts, new Set(['missing']))).toEqual([])
  expect(proposeCountDemand(counts, new Set())).toEqual([])
  const wrongBound = problem().map(c => c.v === 'selected' ? {...c, below: n(5)} : c)
  expect(proposeCountDemand(wrongBound, new Set(['remaining']), {pairs: [['remaining', 'selected']]})).toEqual([])
})

test('demanded region families may be used even without a shared positive primitive', () => {
  const counts = [count('p', at('P')), count('q', at('Q')), ...family('wanted'), ...family('unrelated')]
  const insts = proposeCountDemand(counts, new Set(['p', 'wantedleft']), {pairs: [['p', 'q']]})
  expect(insts).toHaveLength(1)
  expect(signature(insts[0]!)).toBe(termsKey([[1, 'p'], [1, 'q'], [-1, 'wantedleft'], [-1, 'wantedboth'], [-1, 'wantedright']]))
  // This is only a candidate: no pointwise coverage or disjointness is asserted.
  const h = countHyp(counts, insts[0]!)!
  expect(h.op).toBe('or')
  if (h.op === 'or') expect(h.xs[1]!.op).toBe('and')
})

test('requested indicators normalize member variables and equality orientation; both partitions check', () => {
  const counts = [
    count('size', bit(member('A', 'alpha')), 'alpha'),
    count('left', bit(all(same(n(1), at('A', 'beta')), not(member('B', 'beta')))), 'beta'),
    count('both', bit(all(member('A', 'gamma'), member('B', 'gamma'))), 'gamma'),
    ...family('unrelated'),
  ]
  const insts = proposeCountDemand(counts, new Set(['size']), {pairs: []})
  expect(insts).toHaveLength(2)
  expect(insts.map(i => i.terms)).toEqual([
    [[1, 'size'], [-1, 'left'], [-1, 'both']],
    [[-1, 'size'], [1, 'left'], [1, 'both']],
  ])
  prove(counts, insts[0]!, [less(sum(['left', 'both']), x('size'))])
  prove(counts, insts[1]!, [less(x('size'), sum(['left', 'both']))])
  // A region read requests only partitions that contain that region.
  expect(proposeCountDemand(counts, new Set(['left']), {pairs: []}).map(signature)).toEqual(insts.map(signature))
})

test('complement indicators and declared region unions have both partition directions', () => {
  const counts = [...family(''), count('neither', bit(all(not(member('A')), not(member('B'))))),
    count('notA', bit(not(member('A')))), count('either', bit({op: 'or', xs: [member('A'), member('B')]}))]
  const negative = proposeCountDemand(counts, new Set(['notA']), {pairs: []})
  expect(negative.map(i => i.terms)).toEqual([
    [[1, 'notA'], [-1, 'neither'], [-1, 'right']], [[-1, 'notA'], [1, 'neither'], [1, 'right']],
  ])
  const union = proposeCountDemand(counts, new Set(['either']), {pairs: []})
  expect(union.map(signature)).toEqual([
    termsKey([[1, 'either'], [-1, 'left'], [-1, 'both'], [-1, 'right']]),
    termsKey([[-1, 'either'], [1, 'left'], [1, 'both'], [1, 'right']]),
  ])
})

test('a disjoint-cover proposal is admitted by the ordinary checked witness rule', () => {
  const counts = problem()
  const inst = proposeCountDemand(counts, new Set(['remaining', 'selected']))[0]!
  expect(signature(inst)).toBe(target())
  prove(counts, inst, [less(sum(['left', 'both', 'right']), sum(['remaining', 'selected']))])
})

test('raw-map partitions keep the witness alternative instead of asserting an axiom', () => {
  // Fixed cells keep the membership hypotheses independent of the fresh
  // witness (countedOk must reject any original hypothesis naming it).
  const a = same(get('A', n(0)), n(1)), b = same(get('B', n(0)), n(1))
  const counts = [count('size', get('A', n(0))), count('left', bit(all(a, not(b)))), count('both', bit(all(a, b)))]
  const insts = proposeCountDemand(counts, new Set(['size']), {pairs: []})
  expect(insts).toHaveLength(2)
  const inst = insts[0]!, broken = less(sum(['left', 'both']), x('size'))
  prove(counts, inst, [same(get('A', n(0)), n(1)), broken])
  const hyps = [same(get('A', n(0)), n(2)), broken]
  expect(countedOk(hyps, counts, [inst])).toBe(true)
  const goal = countedGoal({name: 'weighted membership is not a set', counts, hyps}, [inst])!
  const proof = grow(goal, new Map(), {nodes: 0, until: clock() + 2000})
  expect('tree' in proof).toBe(false)
  expect('stuck' in proof && proof.stuck).toBe('sat')
})

test('witnesses avoid names from unrelated inputs and caller reservations', () => {
  const counts = [...problem(), count('demand$0', plus(x('demand$1'), n(0)), 'other', n(9))]
  const insts = proposeCountDemand(counts, new Set(['remaining', 'selected']), {reserved: ['demand$2', 'demand$3']})
  expect(insts.length).toBeGreaterThan(0)
  expect(insts.every(i => !['demand$0', 'demand$1', 'demand$2', 'demand$3'].includes(i.wit))).toBe(true)
  expect(countedOk([same(x('demand$2'), n(1))], counts, insts)).toBe(true)
  expect(new Set(insts.map(i => i.wit)).size).toBe(insts.length)
})

test('output and work limits are hard, deterministic, and do not mutate input', () => {
  const counts = [count('p', at('A')), count('q', at('A')), ...Array.from({length: 140}, (_, i) => count(`cover${i}`, at('A')))]
  const before = JSON.stringify(counts), demand = new Set(['p', 'q']), pairs = [['p', 'q']] as const
  const run = (maxFacts: number) => proposeCountDemand(counts, demand, {pairs, maxFacts})
  expect(run(1000)).toHaveLength(128)
  expect(run(3)).toHaveLength(3)
  expect(run(0)).toEqual([])
  expect(run(Number.NaN)).toEqual([])
  expect(run(3)).toEqual(run(3))
  expect(proposeCountDemand(counts, demand, {maxWork: 0})).toEqual([])
  expect(proposeCountDemand(counts, demand, {maxWork: 20})).toEqual([])
  expect(JSON.stringify(counts)).toBe(before)
  expect([...demand]).toEqual(['p', 'q'])
})
