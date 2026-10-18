// Composition (compose.ts): the combinators against runs of their parts, and what they buy, proven by the kernel as it
// is: refinement (an implementation against its spec, broken implementations refused), laws of an interleaving, and
// k-step laws of a composed machine.
import {expect, test} from 'bun:test'
import {type E, type Machine, type State, evalC, interpret, loadJs, plus, x} from './machine.ts'
import {nat, rule, when} from './dsl.ts'
import {count, ever, ghost, interleave, product, refinement, steps, total} from './compose.ts'
import {counterLaws, counterSteps, counters, countdown, escrowLaws, escrowSteps, escrowWatched, ledger, meterRefinement, poolLaws, poolTotal, pooled, transferRefinement, twoPhaseRefinement} from '../examples/composition.ts'
import {proveLaws, proveStepLaws} from '../kernel/prove.ts'
import {authority, lazyAuthority, lazyRefinement} from '../examples/sets.ts'
import {type StepLaw, checkStepLaws} from '../kernel/kernel.ts'

let seed = 7
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
const vv = (name: string): E => ({op: 'var', name}), cc = (value: number): E => ({op: 'const', value})
const term = (d: number, names: string[]): E => {
  const r = rand(d <= 0 ? 2 : 6)
  if (r === 0) return vv(names[rand(names.length)]!)
  if (r === 1) return cc(rand(3))
  if (r === 2) return {op: 'add', a: term(d - 1, names), b: term(d - 1, names)}
  if (r === 3) return {op: 'sub', a: term(d - 1, names), b: term(d - 1, names)}
  if (r === 4) return {op: 'get', map: 'M', key: term(d - 1, names)}
  return {op: 'if', c: {op: '<=', a: term(d - 1, names), b: term(d - 1, names)}, then: term(d - 1, names), else: term(d - 1, names)}
}
const randomMachine = (name: string): Machine => {
  const names = ['p', 'a', 'x', 'y']
  return {name, params: ['p'], inputs: ['a'], state: {x: cc(0), y: vv('p')}, maps: {M: 0},
    step: {flags: {f: {op: '<=', a: vv('x'), b: vv('a')}}, state: {x: {op: 'if', c: {op: 'flag', name: 'f'}, then: term(2, names), else: vv('x')}, y: term(2, names)}, maps: {M: {key: term(1, names), value: term(2, names)}}}}
}
const sideOf = (st: State, p: string): State => ({
  scalars: Object.fromEntries(Object.entries(st.scalars).filter(([n]) => n.startsWith(p)).map(([n, v]) => [n.slice(p.length), v])),
  maps: Object.fromEntries(Object.entries(st.maps).filter(([n]) => n.startsWith(p)).map(([n, v]) => [n.slice(p.length), v])),
})
const cells = (st: State) => JSON.stringify(Object.fromEntries(Object.entries(st.maps).map(([n, c]) => [n, [...c.entries()].filter(([, v]) => v !== 0).sort((a, b) => a[0] - b[0])])))
const same = (a: State, b: State) => JSON.stringify(a.scalars) === JSON.stringify(b.scalars) && cells(a) === cells(b)

test('a product and an interleaving run as their parts do, interpreted and compiled', () => {
  let steps = 0
  for (let trial = 0; trial < 60; trial++) {
    const a = randomMachine('a'), b = randomMachine('b')
    const runs = {a: interpret(a), b: interpret(b), p: interpret(product(a, b)), i: interpret(interleave(a, b)), pc: loadJs(product(a, b)), ic: loadJs(interleave(a, b))}
    const params = {p: rand(3)}
    let sa = runs.a.init(params), sb = runs.b.init(params), sp = runs.p.init(params), si = runs.i.init(params), spc = runs.pc.init(params), sic = runs.ic.init(params)
    let ia = sa, ib = sb
    for (let i = 0; i < 12; i++) {
      const a0 = rand(4), turn = rand(2)
      sa = runs.a.step(params, sa, {a: a0}); sb = runs.b.step(params, sb, {a: a0})
      sp = runs.p.step(params, sp, {a: a0}); spc = runs.pc.step(params, spc, {a: a0})
      if (turn === 0) ia = runs.a.step(params, ia, {a: a0}); else ib = runs.b.step(params, ib, {a: a0})
      si = runs.i.step(params, si, {a: a0, turn}); sic = runs.ic.step(params, sic, {a: a0, turn})
      expect(same(sideOf(sp, 'a_'), sa) && same(sideOf(sp, 'b_'), sb) && same(spc, sp)).toBe(true)
      expect(same(sideOf(si, 'a_'), ia) && same(sideOf(si, 'b_'), ib) && same(sic, si)).toBe(true)
      steps++
    }
  }
  expect(steps).toBe(720)
})

test('refinement: the implementation refines the spec; broken ones are refused', () => {
  const ok = meterRefinement()
  const r = proveStepLaws(ok.machine, ok.laws, ok.stepLaws)
  expect(r).toMatchObject({proven: true, checked: true})
  expect(checkStepLaws(ok.machine, ok.laws, ok.stepLaws, r.proof!)).toBe(true)
  // Sent amounts unclamped, the spec would be sent spends it refuses: the step law fails.
  const noClamp = meterRefinement('no clamp')
  const bad1 = proveStepLaws(noClamp.machine, noClamp.laws, noClamp.stepLaws)
  expect(bad1.proven).toBe(false)
  expect(bad1.failed?.goal).toBe('meter allows the request it is sent @step law')
  // Refusing a spend that exactly fills the cap, the implementation drifts from the spec: the relation fails.
  const strict = meterRefinement('strict')
  const bad2 = proveStepLaws(strict.machine, strict.laws, strict.stepLaws)
  expect(bad2.proven).toBe(false)
  expect(bad2.failed?.goal).toBe('left + used = cap @step')
  // And a run shows it: cap 1, most 1, one spend of 1.
  const run = interpret(strict.machine)
  const st = run.step({cap: 1, most: 1}, run.init({cap: 1, most: 1}), {amount: 1})
  expect(st.scalars.a_left! + st.scalars.b_used!).not.toBe(1)
})

test('refinement: a spec precondition must follow from the implementation\'s', () => {
  const guarded = rule('meter').params({cap: nat, most: nat}).inputs({amount: nat}).state({used: 0})
    .pre(({most, cap}) => most.atMost(cap))
    .flags(({amount, used, cap}) => ({fits: used.plus(amount).atMost(cap)}))
    .step(({used, amount, fits}) => ({used: when(fits, used.plus(amount), used)}))
  const witness = {amount: {op: 'min', a: x('amount'), b: x('most')} as E}
  const relation = [{name: 'left + used = cap', holds: {op: '=', a: plus(x('a_left'), x('b_used')), b: x('cap')} as const}]
  const loose = refinement(countdown().machine, guarded.machine, {relation, witness})
  expect(proveStepLaws(loose.machine, loose.laws, loose.stepLaws).proven).toBe(false) // most <= cap isn't impl's
  const tight = refinement({...countdown().machine, pre: guarded.machine.pre!}, guarded.machine, {relation, witness})
  expect(proveStepLaws(tight.machine, tight.laws, tight.stepLaws)).toMatchObject({proven: true, checked: true})
})

test('interleaving: each side\'s laws hold whoever moves, and k-step laws of the whole', () => {
  expect(proveStepLaws(counters, counterLaws, counterSteps)).toMatchObject({proven: true, checked: true})
  const wrong: StepLaw = {...counterSteps[1]!, name: 'two turns of anyone leave b\'s count', when: undefined}
  expect(proveStepLaws(counters, counterLaws, [wrong]).proven).toBe(false)
})

test('ghosts watch a machine without changing it: the same runs, ever and count as they say, a total the real sum', () => {
  let steps = 0
  for (let trial = 0; trial < 60; trial++) {
    const base = randomMachine('m')
    // A map that starts at 0 everywhere, written at an input key each step: random values, or the DSL's bump shapes.
    const shapes: E[] = [vv('a'), {op: 'add', a: {op: 'get', map: 'M', key: vv('a')}, b: cc(1)}, {op: 'sub', a: {op: 'get', map: 'M', key: vv('a')}, b: vv('a')},
      {op: 'if', c: {op: 'flag', name: 'f'}, then: {op: 'add', a: {op: 'get', map: 'M', key: vv('a')}, b: vv('x')}, else: {op: 'get', map: 'M', key: vv('a')}}]
    const m: Machine = {...base, step: {...base.step, maps: {M: {key: vv('a'), value: rand(2) ? shapes[rand(shapes.length)]! : term(2, ['p', 'a', 'x', 'y'])}}}}
    const g = ghost(m, {fired: ever('fired', {op: 'flag', name: 'f'}), times: count('times', {op: 'flag', name: 'f'}), sum: total(m, 'M', 'sum')})
    const rm = interpret(m), rg = interpret(g), params = {p: rand(3)}
    let sm = rm.init(params), sg = rg.init(params), fired = 0, times = 0
    for (let i = 0; i < 12; i++) {
      const input = {a: rand(4)}
      const f = (sm.scalars.x ?? 0) <= input.a
      sm = rm.step(params, sm, input); sg = rg.step(params, sg, input)
      if (f) { fired = 1; times++ }
      const real = [...(sm.maps.M ?? new Map()).values()].reduce((acc, v) => acc + v, 0)
      expect(same(sideOf({scalars: Object.fromEntries(Object.entries(sg.scalars).filter(([n]) => !['fired', 'times', 'sum'].includes(n))), maps: sg.maps}, ''), sm)).toBe(true)
      expect([sg.scalars.fired, sg.scalars.times, sg.scalars.sum]).toEqual([fired, times, real])
      steps++
    }
  }
  expect(steps).toBe(720)
  expect(() => ghost(randomMachine('m'), {x: ever('x', {op: '=', a: cc(0), b: cc(0)})})).toThrow() // a name the machine has
  expect(() => total({...randomMachine('m'), maps: {M: 1}}, 'M', 's')).toThrow() // a map that starts above 0
})

test('stuttering refinement: on a stutter the spec stays; the two-phase meter refines the meter, the broken one doesn\'t', () => {
  const ok = twoPhaseRefinement()
  const run = interpret(ok.machine), params = {cap: 5, most: 2}
  let st = run.init(params)
  st = run.step(params, st, {op: 0, amount: 3}) // reserve: a step the spec doesn't see
  expect([st.scalars.a_pending, st.scalars.b_used]).toEqual([2, 0])
  st = run.step(params, st, {op: 1, amount: 0}) // charge: the spec spends the reserved 2
  expect([st.scalars.a_used, st.scalars.b_used]).toEqual([2, 2])
  expect(proveStepLaws(ok.machine, ok.laws, ok.stepLaws)).toMatchObject({proven: true, checked: true})
  const bad = twoPhaseRefinement('charges the request')
  expect(proveStepLaws(bad.machine, bad.laws, bad.stepLaws).failed?.goal).toBe('used = used @step')
})

test('laws about whole histories, through ghosts: no refund after a release, in use is what the clients hold', () => {
  expect(proveStepLaws(escrowWatched(), escrowLaws, escrowSteps)).toMatchObject({proven: true, checked: true})
  expect(proveStepLaws(escrowWatched('reopens on a deposit'), escrowLaws, escrowSteps).proven).toBe(false)
  // The broken escrow, on a run: deposit, release, deposit, refund.
  const m = escrowWatched('reopens on a deposit'), run = interpret(m)
  let st = run.init({})
  for (const input of [{op: 0, amount: 2}, {op: 1, amount: 0}, {op: 0, amount: 1}, {op: 2, amount: 0}]) st = run.step({}, st, input)
  expect([st.scalars.released, st.scalars.refunded]).toEqual([1, 1])
  expect(proveLaws(pooled(), [...poolLaws, ...poolTotal])).toMatchObject({proven: true, checked: true})
  expect(proveLaws(pooled('release unchecked'), [...poolLaws, ...poolTotal]).proven).toBe(false)
})

// steps(m, k): one step of it is k steps of m (each skipped where its skip input is 1), on random machines and the ledger;
// and the transfer refines two ledger steps, while the version that forgets a transfer to the same account doesn't.
test('steps(m, k) runs as k steps of m; the transfer refines two ledger steps', () => {
  for (let trial = 0; trial < 60; trial++) {
    const m = trial % 2 ? ledger.machine : randomMachine(`random ${trial}`), k = 1 + rand(3), big = steps(m, k)
    const one = interpret(m), many = interpret(big), compiled = loadJs(big)
    for (let t = 0; t < 10; t++) {
      const params = Object.fromEntries(m.params.map(p => [p, rand(4)]))
      let a = one.init(params), b = many.init(params), g = compiled.init(params)
      for (let i = 0; i < 5; i++) {
        const reqs: Record<string, number>[] = Array.from({length: k}, () => ({...Object.fromEntries(m.inputs.map(n => [n, rand(4)])), skip: rand(3) === 0 ? 1 : 0}))
        const input = Object.fromEntries(reqs.flatMap((r, j) => [...m.inputs.map(n => [`${n}@s${j + 1}`, r[n]!] as const), [`skip@s${j + 1}`, r.skip!] as const]))
        // m's own assumption at each step not skipped decides whether big allows the request.
        const env = (st: State, r: Record<string, number>) => ({...params, ...r})
        let st = a, ok = true
        for (const r of reqs) {
          if (r.skip) continue
          const {skip: _skip, ...req} = r
          if (m.assume && !allowedIn(m, st, env(st, req))) { ok = false; break }
          st = one.step(params, st, req)
        }
        if (!ok) continue
        a = st; b = many.step(params, b, input); g = compiled.step(params, g, input)
        expect(b.scalars).toEqual(a.scalars)
        for (const map of Object.keys(m.maps ?? {})) for (let key = 0; key < 8; key++) {
          const read = (s2: State) => s2.maps[map]!.get(key) ?? s2.defaults?.[map] ?? m.maps![map]!
          expect(read(b)).toBe(read(a))
          expect(read(g)).toBe(read(a))
        }
      }
    }
  }
  const ok = transferRefinement(), r = proveStepLaws(ok.machine, ok.laws, ok.stepLaws)
  expect(r).toMatchObject({proven: true, checked: true})
  const bad = transferRefinement('forgets a transfer to the same account')
  expect(proveStepLaws(bad.machine, bad.laws, bad.stepLaws).proven).toBe(false)
}, 120_000)
const allowedIn = (m: Machine, st: State, env: Record<string, number>): boolean => evalC(m.assume!, env, st, m)

test('refinement over sets: the lazy authority refines the eager one (carried sets shared, every-key writes, flags at every key)', () => {
  const R = lazyRefinement()
  expect(R.machine.inputMaps).toEqual(['Candidate'])
  expect(proveStepLaws(R.machine, R.laws, R.stepLaws)).toMatchObject({proven: true, checked: true})
  const bad = lazyRefinement('keeps the child live on refusal')
  expect(proveStepLaws(bad.machine, bad.laws, bad.stepLaws).proven).toBe(false)
  // Runs: the same requests to both, the relation read on the composite's runs, against the two run on their own.
  const lazy = interpret(lazyAuthority().machine), eager = interpret(authority().machine), both = interpret(R.machine)
  let seed = 9
  const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
  let nonempty = 0
  for (let trial = 0; trial < 40; trial++) {
    let a = lazy.init({}), b = eager.init({}), c = both.init({})
    for (let i = 0; i < 12; i++) {
      // The first request issues all four names; the rest are random, deriving often.
      const Candidate = i === 0 ? new Map([0, 1, 2, 3].map(k => [k, 1] as const)) : new Map(Array.from({length: rand(3)}, () => [rand(4), 1] as const))
      const input = {op: i === 0 ? 0 : [1, 1, 2, 3][rand(4)]!, name: rand(4), Candidate}
      a = lazy.step({}, a, input); b = eager.step({}, b, input); c = both.step({}, c, input)
      for (let k = 0; k < 5; k++) {
        const child = (st: State, map: string) => st.maps[map]?.get(k) ?? st.defaults?.[map] ?? 0
        expect(child(c, 'b_Child')).toBe(child(b, 'Child'))
        expect(child(b, 'Child')).toBe(a.scalars.live === 1 ? child(a, 'Child') : 0)
        if (child(b, 'Child') === 1) nonempty++
      }
    }
  }
  expect(nonempty).toBeGreaterThan(20)
}, 60_000)
