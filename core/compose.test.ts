// Composition (compose.ts): the combinators against runs of their parts, and what they buy, proven by the kernel as it
// is: refinement (an implementation against its spec, broken implementations refused), laws of an interleaving, and
// k-step laws of a composed machine.
import {expect, test} from 'bun:test'
import {type E, type Machine, type State, interpret, loadJs, plus, x} from './machine.ts'
import {nat, rule, when} from './dsl.ts'
import {interleave, product, refinement} from './compose.ts'
import {counterLaws, counterSteps, counters, countdown, meterRefinement} from '../examples/composition.ts'
import {proveStepLaws} from '../kernel/prove.ts'
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
