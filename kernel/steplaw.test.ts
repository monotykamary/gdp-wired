// Step laws (kernel.ts's stepLawObligations): what one step does, for every request the machine allows. Unit cases
// (monotone counters, a `when`, maps at every key, histories' sums, refusals), and a soundness fuzz: random machines and
// random step laws; whenever the kernel accepts one, no run of the interpreter breaks it, and some false ones are caught.
import {expect, test} from 'bun:test'
import type {C, E, Machine, State} from '../core/machine.ts'
import {evalC, interpret} from '../core/machine.ts'
import {forall, maybe, nat, oneOf, proveSteps, rule, upTo, when} from '../core/dsl.ts'
import {windowLimit} from '../core/models.ts'
import {type StepLaw, checkStepLaws, stepLawObligations} from './kernel.ts'
import {proveStepLaws} from './prove.ts'

const counter = rule('counter').params({cap: nat}).inputs({op: oneOf('add', 'reset'), amount: nat}).state({used: 0, resets: 0})
  .flags(({op, amount, used, cap}) => ({fits: op.is('add').and(used.plus(amount).atMost(cap))}))
  .step(({op, amount, used, resets, fits}) => ({used: when(fits, used.plus(amount), when(op.is('reset'), 0, used)), resets: when(op.is('reset'), resets.plus(1), resets)}))

test('step laws: proven when they hold, refused when a step breaks them', () => {
  const grows = counter.stepLaw('an add never lowers used', ({used}, after) => used.atMost(after.used), ({op}) => op.is('add'))
  const exact = counter.stepLaw('a fitting add adds exactly the amount', ({used, amount}, after) => after.used.eq(used.plus(amount)), ({fits}) => fits)
  const resets = counter.stepLaw('resets only count up, by one at most', ({resets}, after) => resets.atMost(after.resets).and(after.resets.atMost(resets.plus(1))))
  expect(proveSteps(counter, [counter.law('used <= cap', ({used, cap}) => used.atMost(cap))], [grows, exact, resets])).toMatchObject({proven: true, checked: true})
  const never = counter.stepLaw('used never goes down', ({used}, after) => used.atMost(after.used)) // a reset lowers it
  expect(proveSteps(counter, [], [never]).proven).toBe(false)
  const flags = counter.stepLaw('fits means used grows', ({used, fits}, after) => fits.implies(used.atMost(after.used)))
  expect(proveSteps(counter, [], [flags]).proven).toBe(true)
})

test('step laws over maps, at every key, and over a history', () => {
  const tally = rule('tally').inputs({who: nat, ok: maybe(upTo(1))}).maps({Votes: 0})
    .step(({who, ok, Votes}) => ({Votes: Votes.bump(who, ok.match({none: () => ok.isSome, some: v => v.eq(1)}))}))
  const onlyUp = tally.stepLaw('no count ever goes down', ({Votes}, after) => forall(k => Votes.at(k).atMost(after.Votes.at(k))))
  const others = tally.stepLaw('a vote moves only its own count', ({who, Votes}, after) => forall(k => k.ne(who).implies(after.Votes.at(k).eq(Votes.at(k)))))
  expect(proveSteps(tally, [], [onlyUp, others])).toMatchObject({proven: true, checked: true})
  const wrong = tally.stepLaw('a vote moves every count', ({Votes}, after) => forall(k => Votes.at(k).lt(after.Votes.at(k))))
  expect(proveSteps(tally, [], [wrong]).proven).toBe(false)
  // The window limit's sum `ours` (admitted requests in the window ending at now) only grows.
  const w = windowLimit()
  const grows: StepLaw = {name: 'ours never shrinks', then: {op: '<=', a: {op: 'var', name: 'ours'}, b: {op: 'var', name: "ours'"}}}
  expect(proveStepLaws(w, [], [grows])).toMatchObject({proven: true, checked: true})
})

test('step laws outside the rule are refused', () => {
  const m = counter.machine
  const sl = (then: C, when?: C): StepLaw => ({name: 'x', then, ...(when ? {when} : {})})
  const v = (name: string): E => ({op: 'var', name}), n = (value: number): E => ({op: 'const', value})
  expect(() => stepLawObligations(m, [], {}, sl({op: '<=', a: v("used'"), b: v('cap')}))).not.toThrow()
  expect(() => stepLawObligations(m, [], {}, sl({op: '<=', a: v("usd'"), b: v('cap')}))).toThrow() // undeclared
  expect(() => stepLawObligations(m, [], {}, sl({op: '<=', a: v('used'), b: n(-1)}))).toThrow() // negative constant
  expect(() => stepLawObligations(m, [], {}, sl({op: '<=', a: v('used'), b: v('cap')}, {op: '<=', a: v("used'"), b: n(1)}))).toThrow() // when reads after
  expect(() => stepLawObligations({...m, inputs: [...m.inputs, "used'"]}, [], {}, sl({op: '<=', a: v('used'), b: v('cap')}))).toThrow() // a primed name taken
})

test('a step-law proof checks only whole: every law tree and every step tree', () => {
  const laws = [counter.law('used <= cap', ({used, cap}) => used.atMost(cap))]
  const stepLaws = [
    counter.stepLaw('an add never lowers used', ({used}, after) => used.atMost(after.used), ({op}) => op.is('add')),
    counter.stepLaw('a fitting add adds exactly the amount', ({used, amount}, after) => after.used.eq(used.plus(amount)), ({fits}) => fits),
  ]
  const r = proveStepLaws(counter.machine, laws, stepLaws)
  expect(r).toMatchObject({proven: true, checked: true})
  const proof = r.proof!
  expect(checkStepLaws(counter.machine, laws, stepLaws, proof)).toBe(true)
  // One step law's tree emptied (the other untouched), or missing; a law's tree emptied: each rejected.
  for (const name of Object.keys(proof.trees)) {
    expect(checkStepLaws(counter.machine, laws, stepLaws, {...proof, trees: {...proof.trees, [name]: {leaf: []}}})).toBe(false)
    const {[name]: _, ...rest} = proof.trees
    expect(checkStepLaws(counter.machine, laws, stepLaws, {...proof, trees: rest})).toBe(false)
  }
  for (const name of Object.keys(proof.laws.trees)) {
    expect(checkStepLaws(counter.machine, laws, stepLaws, {...proof, laws: {...proof.laws, trees: {...proof.laws.trees, [name]: {leaf: []}}}})).toBe(false)
  }
})

// --- soundness fuzz ------------------------------------------------------------------------------------------------------
let seed = Number(process.env.FUZZ_SEED ?? 31)
const scale = Number(process.env.FUZZ_SCALE ?? 1)
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
const pick = <T>(xs: readonly T[]): T => xs[rand(xs.length)]!
const vv = (name: string): E => ({op: 'var', name}), cc = (value: number): E => ({op: 'const', value})
const term = (d: number): E => {
  const r = rand(d <= 0 ? 2 : 6)
  if (r === 0) return vv(pick(['a', 'b', 'p', 'x', 'y']))
  if (r === 1) return cc(rand(3))
  if (r === 2) return {op: 'add', a: term(d - 1), b: term(d - 1)}
  if (r === 3) return {op: 'sub', a: term(d - 1), b: term(d - 1)}
  if (r === 4) return {op: 'min', a: term(d - 1), b: term(d - 1)}
  return {op: 'if', c: {op: pick(['<', '<=', '='] as const), a: term(d - 1), b: term(d - 1)}, then: term(d - 1), else: term(d - 1)}
}
const stepLaws = (): StepLaw[] => {
  const x = vv('x'), y = vv('y'), x1 = vv("x'"), y1 = vv("y'")
  const forms: C[] = [{op: '<=', a: x, b: x1}, {op: '<=', a: x1, b: x}, {op: '<=', a: x1, b: {op: 'add', a: x, b: vv('a')}}, {op: '<=', a: y, b: y1},
    {op: '=', a: x1, b: x}, {op: '<=', a: x1, b: {op: 'add', a: y1, b: vv('p')}}, {op: '<=', a: {op: 'add', a: x, b: y}, b: {op: 'add', a: x1, b: y1}},
    {op: 'or', xs: [{op: '<', a: x, b: x1}, {op: '=', a: y1, b: y}]}, {op: '<=', a: {op: 'get', map: 'M', key: vv('a')}, b: {op: 'get', map: "M'", key: vv('a')}}]
  return forms.map((then, i) => ({name: `form ${i}`, then, ...(rand(3) === 0 ? {when: {op: '<=', a: vv('a'), b: vv('b')} as C} : {})}))
}

test('a step law the kernel accepts holds on every run', () => {
  let proven = 0, refuted = 0, caught = 0, steps = 0
  for (let trial = 0; trial < 120 * scale; trial++) {
    const m: Machine = {name: 'random', params: ['p'], inputs: ['a', 'b'], state: {x: cc(0), y: cc(0)}, maps: {M: 0},
      step: {state: {x: rand(2) ? {op: 'add', a: vv('x'), b: term(1)} : term(2), y: term(2)}, maps: {M: {key: vv('a'), value: rand(2) ? {op: 'add', a: {op: 'get', map: 'M', key: vv('a')}, b: term(1)} : term(1)}}}}
    const run = interpret(m)
    for (const sl of stepLaws()) {
      const ok = proveStepLaws(m, [], [sl])
      ok.proven && ok.checked ? proven++ : refuted++
      // Runs: every state reached, every request (values 0..2), the law read before and after the step.
      let broken = false
      for (let p = 0; p < 3 && !broken; p++) {
        let frontier: State[] = [run.init({p})]
        for (let depth = 0; depth < 3 && !broken; depth++) {
          const next: State[] = []
          for (const st of frontier) for (let a = 0; a < 3; a++) for (let b = 0; b < 3; b++) {
            const input = {a, b}, after = run.step({p}, st, input)
            steps++
            const env = {p, a, b}
            if (sl.when && !evalC(sl.when as C, env, st, m)) { next.push(after); continue }
            const both: State = {scalars: {...st.scalars, "x'": after.scalars.x!, "y'": after.scalars.y!}, maps: {...st.maps, "M'": after.maps.M!}}
            if (!evalC(sl.then, env, both, {...m, maps: {M: 0, "M'": 0}})) broken = true
            next.push(after)
          }
          frontier = next.slice(0, 40)
        }
      }
      if (ok.proven && ok.checked) expect(broken, `${sl.name} on ${JSON.stringify(m.step)}`).toBe(false)
      else if (broken) caught++
    }
  }
  console.log(`step laws: ${proven} proven (none broken by ${steps.toLocaleString()} steps), ${refuted} refused (${caught} of those broken by a run)`)
  expect(proven).toBeGreaterThan(50 * scale)
  expect(caught).toBeGreaterThan(50 * scale)
}, 600_000)

// --- k steps -----------------------------------------------------------------------------------------------------------

test('k-step laws: about several steps in a row, proven from the same moves', () => {
  const laws = [counter.law('used <= cap', ({used, cap}) => used.atMost(cap))]
  const m = counter.machine
  const v = (name: string): E => ({op: 'var', name})
  const add = (a: E, b: E): E => ({op: 'add', a, b})
  // Two fitting adds add exactly both amounts.
  const both: StepLaw = {name: 'two fitting adds', steps: 2, when: [{op: 'flag', name: 'fits'}, {op: 'flag', name: 'fits'}], then: {op: '=', a: v("used'"), b: add(add(v('used'), v('amount')), v('amount@2'))}}
  // After a reset, whatever comes next leaves used at most the next amount: about two steps, not one.
  const resetThen: StepLaw = {name: 'reset, then at most one amount', steps: 2, when: [{op: '=', a: v('op'), b: {op: 'const', value: 1}}], then: {op: '<=', a: v("used'"), b: v('amount@2')}}
  // Three steps never take used past cap (the law, read three steps on).
  const three: StepLaw = {name: 'three steps stay under cap', steps: 3, then: {op: '<=', a: v("used'"), b: v('cap')}}
  const r = proveStepLaws(m, laws, [both, resetThen, three])
  expect(r).toMatchObject({proven: true, checked: true})
  expect(Object.keys(r.proof!.trees)).toEqual(['two fitting adds @2 steps', 'reset, then at most one amount @2 steps', 'three steps stay under cap @3 steps'])
  // False ones: two steps can lower used (a reset), and two adds that don't fit don't add.
  const lowers: StepLaw = {name: 'two steps never lower used', steps: 2, then: {op: '<=', a: v('used'), b: v("used'")}}
  const unfit: StepLaw = {name: 'two adds add both', steps: 2, when: [{op: '=', a: v('op'), b: {op: 'const', value: 0}}, {op: '=', a: v('op'), b: {op: 'const', value: 0}}], then: {op: '=', a: v("used'"), b: add(add(v('used'), v('amount')), v('amount@2'))}}
  expect(proveStepLaws(m, laws, [lowers]).proven).toBe(false)
  expect(proveStepLaws(m, laws, [unfit]).proven).toBe(false)
  // One step is the step law as before: the same goal, by name and hypotheses.
  const one: StepLaw = {name: 'grows', then: {op: '<=', a: v('used'), b: v("used'")}, when: {op: 'flag', name: 'fits'}}
  expect(stepLawObligations(m, laws, {}, {...one, steps: 1})).toEqual(stepLawObligations(m, laws, {}, one))
})

test('k-step laws outside the rule are refused', () => {
  const m = counter.machine
  const v = (name: string): E => ({op: 'var', name})
  const sl = (steps: number, then: C, when?: C | C[]): StepLaw => ({name: 'x', steps, then, ...(when ? {when} : {})})
  const le = (a: E, b: E): C => ({op: '<=', a, b})
  expect(() => stepLawObligations(m, [], {}, sl(2, le(v("used'"), v('amount@2'))))).not.toThrow()
  expect(() => stepLawObligations(m, [], {}, sl(2, le(v("used'"), v('amount@3'))))).toThrow() // no third request
  expect(() => stepLawObligations(m, [], {}, sl(0, le(v("used'"), v('cap'))))).toThrow()
  expect(() => stepLawObligations(m, [], {}, sl(64, le(v("used'"), v('cap'))))).not.toThrow() // 64 steps at most
  expect(() => stepLawObligations(m, [], {}, sl(65, le(v("used'"), v('cap'))))).toThrow()
  expect(() => stepLawObligations(m, [], {}, sl(1.5, le(v("used'"), v('cap'))))).toThrow()
  expect(() => stepLawObligations(m, [], {}, sl(2, le(v("used'"), v('cap')), [le(v('used'), v('cap')), le(v('used'), v('cap')), le(v('used'), v('cap'))]))).toThrow() // a when per step at most
  expect(() => stepLawObligations(m, [], {}, sl(2, le(v("used'"), v('cap')), [le(v('used'), v('cap')), le(v('amount@2'), v('cap'))]))).toThrow() // a when reads its own request plainly
  expect(() => stepLawObligations({...m, inputs: [...m.inputs, 'amount@2']}, [], {}, sl(2, le(v("used'"), v('cap'))))).toThrow() // a later name taken
})

test('a k-step law the kernel accepts holds on every run of k steps', () => {
  let proven = 0, refuted = 0, caught = 0, runs = 0
  const x = vv('x'), y = vv('y'), x1 = vv("x'"), y1 = vv("y'"), a = vv('a'), a2 = vv('a@2')
  const forms: C[] = [{op: '<=', a: x, b: x1}, {op: '<=', a: x1, b: {op: 'add', a: {op: 'add', a: x, b: a}, b: a2}}, {op: '=', a: x1, b: x},
    {op: '<=', a: {op: 'add', a: x, b: y}, b: {op: 'add', a: x1, b: y1}}, {op: '<=', a: {op: 'get', map: 'M', key: a}, b: {op: 'get', map: "M'", key: a}},
    {op: '<=', a: {op: 'get', map: "M'", key: a2}, b: {op: 'add', a: {op: 'get', map: 'M', key: a2}, b: {op: 'mul', k: 2, a: {op: 'add', a: vv('p'), b: cc(1)}}}}]
  for (let trial = 0; trial < 40 * scale; trial++) {
    const m: Machine = {name: 'random', params: ['p'], inputs: ['a', 'b'], state: {x: cc(0), y: cc(0)}, maps: {M: 0},
      step: {state: {x: rand(2) ? {op: 'add', a: vv('x'), b: term(1)} : term(2), y: term(2)}, maps: {M: {key: vv('a'), value: rand(2) ? {op: 'add', a: {op: 'get', map: 'M', key: vv('a')}, b: term(1)} : term(1)}}}}
    const run = interpret(m)
    for (const [i, then] of forms.entries()) {
      const k = 2 + rand(2)
      const sl: StepLaw = {name: `form ${i}`, steps: k, then, ...(rand(3) === 0 ? {when: [{op: '<=', a: vv('a'), b: vv('b')} as C]} : {})}
      const ok = proveStepLaws(m, [], [sl])
      ok.proven && ok.checked ? proven++ : refuted++
      // Every reachable state (two steps deep), then every k requests from it (values 0..2).
      let broken = false
      for (let p = 0; p < 3 && !broken; p++) {
        let frontier: State[] = [run.init({p})]
        const reached: State[] = [...frontier]
        for (let d = 0; d < 2; d++) { frontier = frontier.flatMap(st => [0, 1, 2].map(av => run.step({p}, st, {a: av, b: 1}))).slice(0, 12); reached.push(...frontier) }
        const reqs: Record<string, number>[] = []
        for (let av = 0; av < 3; av++) for (let bv = 0; bv < 3; bv++) reqs.push({a: av, b: bv})
        for (const st of reached) {
          const walk = (cur: State, taken: Record<string, number>[]) => {
            if (broken) return
            if (taken.length === k) {
              runs++
              const env: Record<string, number> = {p, ...taken[0]!}
              taken.slice(1).forEach((t, j) => { env[`a@${j + 2}`] = t.a!; env[`b@${j + 2}`] = t.b! })
              const both: State = {scalars: {...st.scalars, "x'": cur.scalars.x!, "y'": cur.scalars.y!}, maps: {...st.maps, "M'": cur.maps.M!}}
              if (!evalC(sl.then, env, both, {...m, maps: {M: 0, "M'": 0}})) broken = true
              return
            }
            for (const req of reqs) {
              if (taken.length === 0 && Array.isArray(sl.when) && !evalC(sl.when[0]!, {p, ...req}, cur, m)) continue
              walk(run.step({p}, cur, req), [...taken, req])
            }
          }
          walk(st, [])
          if (broken) break
        }
      }
      if (ok.proven && ok.checked) expect(broken, `${sl.name} over ${k} steps on ${JSON.stringify(m.step)}`).toBe(false)
      else if (broken) caught++
    }
  }
  console.log(`k-step laws: ${proven} proven (none broken by ${runs.toLocaleString()} runs of k steps), ${refuted} refused (${caught} of those broken by a run)`)
  expect(proven).toBeGreaterThan(10 * scale)
  expect(caught).toBeGreaterThan(10 * scale)
}, 600_000)
