import {expect, test} from 'bun:test'
import {everyKey, exists, forall, nat, oneOf, proveRule, rule, when, yes} from './dsl.ts'
import {cpair, evalC, interpret, type Law, type State} from './machine.ts'
import {skolemOf, small, smallOf, witnessSupport} from './exists.ts'
import {proveLaw, proveSetFast, withWall} from '../kernel/prove.ts'

// A generic row join with a forgotten input and two forwarding stages. No
// helper invariant or ghost is supplied to the public proof request.
const pipeline = (broken = false) => rule('row pipeline')
  .sorts('Actor', 'Item', 'Label', 'Token')
  .relations({Allows: ['Item', 'Label'], Offers: ['Actor', 'Item'], Mail: ['Actor', 'Label'], Seen: ['Actor', 'Label'], Pending: ['Token', 'Item'], Answers: ['Token', 'Label'], Owners: ['Token', 'Actor']})
  .inputs({op: oneOf('allow', 'start', 'offer', 'receive', 'attach', 'answer', 'send'), a: nat, x: nat, y: nat, t: nat})
  .assume(({a, x, y, t}) => a.lt(64).and(x.lt(64), y.lt(64), t.lt(64)))
  .state({active: 0})
  .flags(({t, Owners}) => ({fresh: everyKey(a => a.lt(64).implies(Owners.has(t, a).not()))}))
  .flags(({op, a, x, y, t, active, fresh, Offers, Allows, Pending, Answers, Owners, Mail}) => ({
    allowing: op.is('allow').and(active.eq(0)), starting: op.is('start').and(active.eq(0)),
    offering: op.is('offer').and(active.eq(1)),
    attaching: op.is('attach').and(active.eq(1), Offers.has(a, x), fresh),
    answering: op.is('answer').and(active.eq(1), Pending.has(t, x), broken ? yes : Allows.has(x, y)),
    sending: op.is('send').and(active.eq(1), Answers.has(t, y), Owners.has(t, a)),
    receiving: op.is('receive').and(active.eq(1), Mail.has(a, y)),
  }))
  .step(({a, x, y, t, active, allowing, starting, offering, attaching, answering, sending, receiving, Allows, Offers, Pending, Answers, Owners, Mail, Seen}) => ({
    active: when(starting, 1, active), Allows: Allows.add([x, y], allowing), Offers: Offers.add([a, x], offering),
    Mail: Mail.add([a, y], sending), Seen: Seen.add([a, y], receiving), Pending: Pending.add([t, x], attaching),
    Answers: Answers.add([t, y], answering), Owners: Owners.add([t, a], attaching),
  }))
const safety = (r: ReturnType<typeof pipeline>) => r.law('seen labels have an offered allowed item', ({Seen, Offers, Allows}) => forall((a, y) =>
  a.lt(64).and(y.lt(64), Seen.has(a, y)).implies(exists(x => x.lt(64).and(Offers.has(a, x), Allows.has(x, y))))))

const holds = (m: ReturnType<typeof pipeline>['machine'], l: Law, s: State) => {
  const ns = [l.forall!, ...(l.keys ?? [])]
  const go = (i: number, env: Record<string, number>): boolean => i === ns.length ? evalC(l.holds, env, s, m)
    : [0, 1, 2, 3].every(x => go(i + 1, {...env, [ns[i]!]: x}))
  return go(0, {})
}

test('an orphan row is a genuine induction counterexample, not a reachable trace', () => {
  const r = pipeline(), m = r.machine, run = interpret(m), s = run.init({})
  const agreement = r.law('joined rows agree', ({Pending, Owners, Offers}) => forall((t, x, a) => Pending.has(t, x).and(Owners.has(t, a)).implies(Offers.has(a, x))))
  s.scalars.active = 1; s.maps.Pending!.set(cpair(0, 0), 1); s.maps.Offers!.set(cpair(0, 1), 1)
  expect(holds(m, agreement, s)).toBe(true)
  expect(holds(m, agreement, run.step({}, s, {op: 4, t: 0, a: 0, x: 1, y: 0}))).toBe(false)
  const sk = skolemOf(m, [safety(r)])!
  expect(sk.ok(m)).toBe(true)
  const provenance = sk.cands.find(l => l.name.startsWith('Pending$g where'))!
  expect(provenance).toBeDefined()
  const ghosted = sk.ghost(m), gs = {...s, maps: {...s.maps, ...Object.fromEntries(Object.keys(sk.maps).map(n => [n, new Map<number, number>()]))}}
  expect(holds(ghosted, provenance, gs)).toBe(false)
}, 30000)

test('co-write provenance closes a renamed forwarding pipeline with nothing written', () => {
  const r = pipeline()
  expect(withWall(performance.now() + 60000, () => proveRule(r, [safety(r)], {search: {ms: 60000}}))).toMatchObject({proven: true, checked: true})
  const bad = pipeline(true)
  expect(withWall(performance.now() + 15000, () => proveRule(bad, [safety(bad)], {search: {ms: 15000}})).proven).toBe(false)
}, 90000)

test('support subsets follow flag dependencies and exclude downstream laws', () => {
  const r = pipeline(), sk = skolemOf(r.machine, [safety(r)])!, m = sk.ghost(r.machine), ls = [...sk.laws, ...sk.cands]
  const source = sk.laws.find(l => l.name.includes('where Mail is set'))!
  const local = witnessSupport(m, ls, source)
  expect(local).toContain(source)
  expect(local).not.toContain(sk.laws[0]!)
  expect(local.some(l => l.name.includes('Answers$g'))).toBe(true)
}, 30000)

test('small instances sample an empty parameter valuation once, retaining distinct valuations', () => {
  const m = rule('sample cache').inputs({x: nat}).assume(({x}) => x.lt(2)).state({n: 0}).step(({x}) => ({n: x})).machine
  const instances = smallOf(m)
  expect(instances).toHaveLength(1)
  expect(instances[0]!.p).toEqual({})
  expect(instances[0]!.sts).toEqual(small(m, {}, 3, 3000, 300_000, 100_000))
  expect(smallOf(m)).toBe(instances)
  const pm = rule('parameter samples').params({cap: nat}).state({n: 0}).step(({cap}) => ({n: cap})).machine
  const parameterized = smallOf(pm)
  expect(parameterized.map(x => x.p)).toEqual([{cap: 2}, {cap: 3}])
  expect(parameterized.map(x => x.sts.at(-1)!.scalars.n)).toEqual([2, 3])
})

test('memoized proof support is invalidated by changed laws and machines', () => {
  const r = rule('memo support').inputs({x: nat}).state({n: 0}).step(({x}) => ({n: x}))
  const good = r.law('claim', ({n}) => n.atLeast(0))
  expect(proveLaw(r.machine, [good], 0).proven).toBe(true)
  expect(proveSetFast(r.machine, [good])).toMatchObject({proven: true, checked: true})
  const bad = r.law('claim', ({n}) => n.eq(0))
  expect(proveSetFast(r.machine, [bad]).proven).toBe(false)
  const changed = {...r.machine, state: {n: {op: 'const' as const, value: 1}}}
  expect(proveSetFast(changed, [bad]).proven).toBe(false)
})
