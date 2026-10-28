// Sums over a map's keys (kernel.ts's sumMachine, Sums.lean) and liveness under strong fairness (kernel.ts's
// livenessParts, Live.lean's sleads_sf_soundA): the runtimes keep every sum exact, the kernel proves laws over sums and
// cells against them, and refuses what isn't a sum it can keep exact, a law that is false, and a liveness that holds
// under no fairness.
import {expect, test} from 'bun:test'
import {bool, forall, nat, no, oneOf, proveLeadsTo, proveRule, rule, when, yes} from './dsl.ts'
import {type Machine, interpret, loadJs, seeded} from './machine.ts'
import {check, checkLaws, checkStepLaws, livenessParts, sideGoals, sumMachine} from '../kernel/kernel.ts'
import {proveLaws, proveLiveness} from '../kernel/prove.ts'

const token = (bug?: 'free mint') => rule('token')
  .inputs({op: oneOf('mint', 'transfer', 'burn'), from: nat, to: nat, value: nat})
  .state({supply: 0})
  .maps({Bal: 0})
  .flags(({op, from, value, Bal}) => ({mints: op.is('mint'), transfers: op.is('transfer').and(Bal.at(from).atLeast(value)), burns: op.is('burn').and(Bal.at(from).atLeast(value))}))
  .step(({from, to, value, supply, Bal, mints, transfers, burns}) => ({
    Bal: Bal.each(k => Bal.at(k).minus(when(transfers.or(burns).and(k.eq(from)), value, 0)).plus(when(mints.or(transfers).and(k.eq(to)), value, 0))),
    supply: when(mints, bug ? supply : supply.plus(value), when(burns, supply.minus(value), supply)),
  }))

test('the runtimes keep every sum exact', () => {
  const r = token(), law = r.law('sum', ({Bal, supply}) => Bal.sum().eq(supply))
  const m = r.withSumsOf(law).machine, it = interpret(m), js = loadJs(m), rand = seeded(5)
  let a = it.init({}), b = js.init({})
  for (let i = 0; i < 400; i++) {
    const req = {op: rand(3), from: rand(5), to: rand(5), value: rand(4)}
    a = it.step({}, a, req); b = js.step({}, b, req)
    const cells = [...a.maps.Bal!.values()].reduce((x, y) => x + y, 0)
    expect(a.scalars['sum$Bal']).toBe(cells)
    expect(b.scalars['sum$Bal']).toBe(cells)
    expect(a.scalars.supply).toBe(cells)
  }
})

test('laws over a sum and over cells against it are proven; false ones refused with a run', () => {
  const r = token(), sum = r.law('the balances sum to the supply', ({Bal, supply}) => Bal.sum().eq(supply))
  const cell = r.law('no balance exceeds the supply', ({Bal, supply}) => forall(k => Bal.at(k).atMost(supply)))
  const v = proveRule(r, [sum, cell], {search: false})
  expect(v.proven && v.checked).toBe(true)
  // The cell law alone: the search adds the map's sum and finds its law.
  const alone = proveRule(r, [cell])
  expect(alone.proven && alone.checked).toBe(true)
  const b = token('free mint'), bv = proveRule(b, [b.law('the balances sum to the supply', ({Bal, supply}) => Bal.sum().eq(supply))])
  expect(bv.proven).toBe(false)
  expect(bv.run).toBeDefined()
  const tooTight = proveRule(r, [r.law('the balances sum to at most 3', ({Bal}) => Bal.sum().atMost(3))])
  expect(tooTight.proven).toBe(false)
  expect(tooTight.run).toBeDefined()
})

// Up to 0.30.0 a law reading M.sum() added the sum to its rule and to every rule made from it, before or after: they
// decoded and compiled with a sum$M field, and crossCheck failed on it ("the step writes sum$Bal = 0 by its callback, 4
// by the machine"). Now a law changes no rule; the prover entries and crossCheck take the sums the laws read.
test('a law over a sum leaves its rule as it was; crossCheck follows the sum', () => {
  // (a copy of the token's step whose mint forgets the supply)
  const freeMint = (x: ReturnType<typeof token>) => x.step(({from, to, value, supply, Bal, mints, transfers, burns}) => ({
    Bal: Bal.each(k => Bal.at(k).minus(when(transfers.or(burns).and(k.eq(from)), value, 0)).plus(when(mints.or(transfers).and(k.eq(to)), value, 0))),
    supply: when(burns, supply.minus(value), supply),
  }))
  const r = token(), before = r.step(({supply}) => ({supply}) as never), early = freeMint(r), shown = (x: {machine: Machine}) => JSON.stringify([Object.keys(x.machine.state), x.machine.sums ?? null])
  const was = [shown(r), shown(before)]
  const sum = r.law('the balances sum to the supply', ({Bal, supply}) => Bal.sum().eq(supply))
  const cell = r.law('no balance exceeds the supply', ({Bal, supply}) => forall(k => Bal.at(k).atMost(supply)))
  const after = r.step(({supply}) => ({supply}) as never)
  expect([shown(r), shown(before)]).toEqual(was)
  expect(shown(after)).toBe(was[1]!)
  expect(Object.keys(r.compiled().init({}).scalars)).toEqual(['supply'])
  expect(Object.keys(r.decode(r.interpreter().init({})))).toEqual(['supply'])
  expect(r.crossCheck([sum, cell])).toEqual({checked: expect.any(Number)})
  expect(proveRule(r, [sum, cell], {search: false})).toMatchObject({proven: true, checked: true})
  // a variant made from the rule before the laws, and one made after: each refused with a run
  for (const b of [early, freeMint(r)]) {
    const v = proveRule(b, [sum], {search: false})
    expect(v.proven).toBe(false)
    expect(v.run).toBeDefined()
  }
  // a sum the rule's own flags read: no callback writes it either
  const capped = rule('capped').inputs({k: nat}).params({cap: nat}).maps({M: 0})
    .flags(({k, cap, M}) => ({adds: M.sum().lt(cap).and(M.at(k).eq(0))}))
    .step(({k, M, adds}) => ({M: M.set(k, when(adds, 1, M.at(k)))}))
  expect(capped.crossCheck([capped.law('at most cap', ({M, cap}) => M.sum().atMost(cap))])).toEqual({checked: expect.any(Number)})
})

// A yes/no map written at every key (the DSL reads each other cell as 1 where it is 1, else 0): its sum's cover goal
// holds only where the cells are at most 1, which their kind's law says (Sums.lean's cellLaws and sum_cells). The cover
// goal assumes the laws about the cells at one key, read at its key, and no other law.
test('a sum over yes/no cells: its cover goal leans on their kind, and on nothing else', () => {
  const r = rule('one holder').inputs({op: oneOf('take', 'give'), n: nat}).maps({Holds: bool.from(false)})
    .flags(({op, Holds}) => ({takes: op.is('take').and(Holds.sum(c => c.n).eq(0)), gives: op.is('give')}))
    .step(({n, takes, gives, Holds}) => ({Holds: Holds.each(k => when(takes.and(k.eq(n)), yes, when(gives.and(k.eq(n)), no, Holds.at(k))))}))
  const law = r.law('one holder at most', ({Holds}) => Holds.sum(c => c.n).atMost(1))
  expect(proveRule(r, [law], {search: false})).toMatchObject({proven: true, checked: true})
  const m = r.withSumsOf(law).machine, kinds = r.kindLaws(), laws = [...kinds, law]
  const covers = (ls: typeof laws) => sideGoals(m, ls).filter(g => g.name.includes('@cover'))
  expect(covers(laws).map(g => g.hyps.length)).toEqual(covers([law]).map(g => g.hyps.length + 1))
  const v = proveLaws(m, laws)
  expect(v.proven && v.checked).toBe(true)
  // Without the kind among the laws, the cover goal is false (a cell at 2 read as 0) and its tree is refused.
  const without = proveLaws(m, [law])
  expect(without.proven).toBe(false)
  expect(without.failed?.goal).toMatch(/@cover Holds/)
  const [g1] = covers(laws), [g0] = covers([law]), tree = v.proof!.trees[g1!.name]!
  expect(check(g1!, tree)).toBe(true)
  expect(check(g0!, tree)).toBe(false)
  expect(checkLaws(m, [law], v.proof!)).toBe(false)
  // The kind read with a further key, or reading a variable, is no law about the cells at one key.
  const [kind] = kinds
  for (const k2 of [{...kind!, keys: ['k$z']}, {...kind!, holds: {op: '<=', a: (kind!.holds as unknown as {a: never}).a, b: {op: 'add', a: {op: 'const', value: 1}, b: {op: 'mul', k: 0, a: {op: 'var', name: 'n'}}}}} as typeof kind])
    expect(covers([k2!, law])).toEqual(covers([law]))
  // A sum over naturals: its laws are about the supply, so its cover goals are as they were.
  const t = token(), cell = t.law('no balance exceeds the supply', ({Bal, supply}) => forall(k => Bal.at(k).atMost(supply)))
  const tm = t.withSumsOf(t.law('the balances sum to the supply', ({Bal, supply}) => Bal.sum().eq(supply))).machine
  expect(sideGoals(tm, [...t.kindLaws(), cell])).toEqual(sideGoals(tm))
})

test('a sum the kernel cannot keep exact is refused', () => {
  const base = token().machine
  const sumOf = (m: Machine, term: unknown): Machine => ({...m, state: {...m.state, S: {op: 'const', value: 0}}, sums: {S: {key: 'k$S', term: term as never}}})
  const cell = {op: 'get', map: 'Bal', key: {op: 'var', name: 'k$S'}}
  // a map that doesn't start at 0, a term reading anything but its maps at its key, a sum the step sets
  expect(() => sumMachine(sumOf({...base, maps: {Bal: 1}}, cell))).toThrow(/not 0 at the start/)
  expect(() => sumMachine(sumOf(base, {op: 'add', a: cell, b: {op: 'var', name: 'supply'}}))).toThrow(/reads the maps at/)
  expect(() => sumMachine(sumOf(base, {op: 'get', map: 'Bal', key: {op: 'add', a: {op: 'var', name: 'k$S'}, b: {op: 'const', value: 1}}}))).toThrow(/reads the maps at/)
  const set = sumOf(base, cell)
  expect(() => sumMachine({...set, step: {...set.step, state: {...set.step.state, S: {op: 'const', value: 0}}}})).toThrow(/no step sets it/)
  // a write at every key that moves every cell: no cover keys, and its cover goal is false, so no law about the sum
  // is proven (here the sum would be infinite)
  const shift: Machine = {...set, step: {...set.step, maps: {Bal: {each: 'k$1', value: {op: 'add', a: {op: 'get', map: 'Bal', key: {op: 'var', name: 'k$1'}}, b: {op: 'const', value: 1}}}}}}
  const r = proveLaws(shift, [{name: 'the sum is the supply', holds: {op: '=', a: {op: 'var', name: 'S'}, b: {op: 'var', name: 'supply'}}}])
  expect(r.proven).toBe(false)
})

test('a seat count never passes the capacity; a booking without the check is refused', () => {
  const seats = (bug?: 'no check') => rule('seats').params({capacity: nat}).inputs({op: oneOf('book', 'cancel'), seat: nat}).maps({Taken: 0})
    .flags(({op, seat, capacity, Taken}) => ({books: op.is('book').and(Taken.at(seat).eq(0), bug ? yes : Taken.sum().lt(capacity)), cancels: op.is('cancel')}))
    .step(({seat, Taken, books, cancels}) => ({Taken: Taken.set(seat, when(books, 1, when(cancels, 0, Taken.at(seat))))}))
  const s = seats(), v = proveRule(s, [s.law('bits', ({Taken}) => forall(k => Taken.at(k).atMost(1))), s.law('capacity', ({Taken, capacity}) => Taken.sum().atMost(capacity))], {search: false})
  expect(v.proven && v.checked).toBe(true)
  const b = seats('no check'), bv = proveRule(b, [b.law('capacity', ({Taken, capacity}) => Taken.sum().atMost(capacity))])
  expect(bv.proven).toBe(false)
  expect(bv.run).toBeDefined()
})

// A job a worker takes and loses again and again: it ends under strong fairness, not under weak; with a stall that may
// lose it for good, under neither.
const job = (bug?: 'lost') => rule('flaky job').inputs({op: oneOf('fetch', 'stall', 'fail', 'lose')})
  .state({st: (bug ? oneOf('wait', 'active', 'failed', 'lost') : oneOf('wait', 'active', 'failed')).from('wait')})
  .flags(({op, st}) => ({fetches: op.is('fetch').and(st.is('wait')), stalls: op.is('stall').and(st.is('active')), fails: op.is('fail').and(st.is('active')), loses: op.is('lose').and(st.is('active'))}))
  .step(({st, fetches, stalls, fails, loses}) => ({st: when(fetches, 'active', when(stalls, 'wait', when(fails, 'failed', bug ? when(loses, 'lost', st) : st)))}))
const ends = (r: ReturnType<typeof job>, fairness?: 'strong') => r.leadsTo('the job fails for good', {from: ({st}) => st.is('failed').not(), to: ({st}) => st.is('failed'), rank: () => 0,
  helpful: [{when: ({st}) => st.is('wait'), request: () => ({op: 0})}, {when: ({st}) => st.is('active'), request: () => ({op: 2})}], ...(fairness ? {fairness} : {})})

test('strong fairness: a helpful request hands over to a higher region; weak fairness proves nothing here', () => {
  const j = job()
  expect(proveLeadsTo(j, j.kindLaws(), ends(j)).proven).toBe(false)
  const strong = proveLiveness(j.machine, j.kindLaws(), ends(j, 'strong'))
  expect(strong.proven && strong.checked).toBe(true)
  expect(strong.levels).toEqual([0, 1])
  // The certificate's step laws again, and with the levels tampered: refused.
  const l = {...ends(j, 'strong'), levels: strong.levels!}, parts = (x: typeof l) => { const p = livenessParts(j.machine, x); return [p.stay, p.cover, ...p.helps] }
  expect(checkStepLaws(j.machine, j.kindLaws(), parts(l), strong.steps!.proof!)).toBe(true)
  for (const levels of [[1, 0], [0, 0]]) expect(checkStepLaws(j.machine, j.kindLaws(), parts({...l, levels}), strong.steps!.proof!)).toBe(false)
  const b = job('lost')
  expect(proveLeadsTo(b, b.kindLaws(), ends(b, 'strong')).proven).toBe(false)
})
