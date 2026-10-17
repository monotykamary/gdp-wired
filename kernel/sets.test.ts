// Sets (maps of 0/1 cells, maps a request carries, quantified flags, writes at every key): the derived authority of
// examples/sets.ts proven and its broken variants refused at the goal they break; the interpreter, the compiled code and
// core/watch.ts agree on random runs, and every broken variant is broken by a run; the kernel's refusals; a proof whose
// flag instances are dropped no longer checks; and a fuzz: random machines over sets, every law the kernel accepts holds
// on every run.
import {expect, test} from 'bun:test'
import {type C, type E, type Law, type Machine, type Request, type State, interpret, loadJs} from '../core/machine.ts'
import {allowed, watch} from '../core/watch.ts'
import {authority, authorityLaws, authorityPairs, authoritySteps} from '../examples/sets.ts'
import {type StepLaw, checkStepLaws, obligations, stepLawObligations} from './kernel.ts'
import {proveLaws, proveStepLaws} from './prove.ts'

let seed = 11
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
const cells = (st: State) => JSON.stringify(Object.fromEntries(Object.entries(st.maps).map(([n, c]) => [n, [...c.entries()].sort((a, b) => a[0] - b[0])]))) + JSON.stringify(st.defaults ?? {})

test('the derived authority: proven; each broken variant refused where it breaks', () => {
  const ok = authority(), r = proveStepLaws(ok.machine, authorityLaws(ok), [...authoritySteps(ok), ...authorityPairs(ok)])
  expect(r).toMatchObject({proven: true, checked: true})
  const named = authority('checks only the named grant')
  expect(proveStepLaws(named.machine, authorityLaws(named), authoritySteps(named)).failed?.goal).toBe('the child is within the grants @step')
  const keeps = authority('keeps the child on refusal')
  expect(proveStepLaws(keeps.machine, authorityLaws(keeps), authoritySteps(keeps)).failed?.goal).toBe('a refused derivation leaves no live child @step law')
})

// Random runs: the interpreter and the compiled code side by side, every law and step law read along the run.
function runs(bug: Parameters<typeof authority>[0], trials: number) {
  const a = authority(bug), m = a.machine, run = interpret(m), gen = loadJs(m)
  const laws: (Law | StepLaw)[] = [...authorityLaws(a), ...authoritySteps(a), ...authorityPairs(a)]
  let steps = 0
  for (let t = 0; t < trials; t++) {
    let st = run.init({}), g = gen.init({})
    const on = laws.map(l => ({name: l.name, w: watch(m, run, l, {}, 4)}))
    for (let i = 0; i < 10; i++) {
      const input: Request = {...a.encodeInput({op: (['issue', 'derive', 'use', 'release'] as const)[rand(4)]!, name: rand(4), Candidate: [0, 1, 2, 3].filter(() => rand(2) === 1)})}
      if (!allowed(m, run, {}, st, input)) continue
      const before = st
      st = run.step({}, st, input); g = gen.step({}, g, input)
      steps++
      if (JSON.stringify(st.scalars) !== JSON.stringify(g.scalars) || cells(st) !== cells(g)) return {steps, mismatch: `${cells(st)} vs ${cells(g)}`}
      for (const l of on) if (!l.w.step(before, input, st)) return {steps, broken: l.name}
    }
  }
  return {steps}
}
test('runs: interpreted = compiled, the proven laws hold, every broken variant is broken by a run', () => {
  const good = runs(undefined, 400)
  expect(good.mismatch).toBeUndefined()
  expect(good.broken).toBeUndefined()
  expect(good.steps).toBeGreaterThan(1000)
  expect(runs('checks only the named grant', 400).broken).toBe('the child is within the grants')
  expect(runs('keeps the child on refusal', 400).broken).toBe('a refused derivation leaves no live child')
})

test('the kernel refuses sets outside the rule', () => {
  const v = (name: string): E => ({op: 'var', name}), k0: E = {op: 'const', value: 0}
  const base: Machine = {name: 'm', params: [], inputs: ['a'], state: {s: k0}, maps: {M: 0}, inputMaps: ['I'], step: {state: {s: v('s')}}}
  const all = (c: C): C => ({op: 'all', key: 'k', c})
  const at = (map: string, key: E): E => ({op: 'get', map, key})
  expect(() => obligations({...base, step: {flags: {f: all({op: '<=', a: at('I', v('k')), b: at('M', v('k'))})}, state: {s: v('s')}}}, [])).not.toThrow()
  expect(() => obligations({...base, assume: all({op: '<=', a: at('I', v('k')), b: {op: 'const', value: 1}})}, [])).toThrow() // a quantifier outside a flag
  expect(() => obligations({...base, step: {flags: {f: all({op: '<=', a: v('k'), b: v('a')})}, state: {s: v('s')}}}, [])).toThrow() // the key in arithmetic
  expect(() => obligations({...base, step: {flags: {f: all({op: '<=', a: at('I', {op: 'add', a: v('k'), b: k0}), b: k0})}, state: {s: v('s')}}}, [])).toThrow() // the key inside a sum
  expect(() => obligations({...base, step: {flags: {f: all({op: 'not', x: all({op: '<=', a: at('M', v('k')), b: k0})})}, state: {s: v('s')}}}, [])).toThrow() // a quantifier inside one
  expect(() => obligations({...base, step: {maps: {M: {each: 's', value: at('I', v('s'))}}}}, [])).toThrow() // the key a name of the machine
  expect(() => obligations({...base, step: {maps: {I: {each: 'k', value: k0}}}}, [])).toThrow() // a carried map written
  expect(() => obligations(base, [{name: 'reads I', holds: {op: '<=', a: at('I', k0), b: k0}}])).toThrow() // a law about a request's map
  // A history, with each kind of set alone.
  const history = {keep: {op: '<=', a: k0, b: k0} as C, record: ['a'], sums: {}, queries: {}}, plain = {...base, inputMaps: []}
  expect(() => obligations({...plain, history}, [])).not.toThrow()
  expect(() => obligations({...base, history}, [])).toThrow()
  expect(() => obligations({...plain, history, step: {flags: {f: all({op: '<=', a: at('M', v('k')), b: k0})}, state: {s: v('s')}}}, [])).toThrow()
  expect(() => obligations({...plain, history, step: {state: {s: v('s')}, maps: {M: {each: 'k', value: k0}}}}, [])).toThrow()
})

test('a proof checks only with the instances it was made with', () => {
  const a = authority(), m = a.machine, laws = authorityLaws(a), steps = authoritySteps(a)
  const r = proveStepLaws(m, laws, steps)
  expect(checkStepLaws(m, laws, steps, r.proof!)).toBe(true)
  // Dropping a quantified flag's instances weakens the goals the trees were grown for: the proof no longer checks.
  const dropped = {...r.proof!, laws: {...r.proof!.laws, instances: Object.fromEntries(Object.entries(r.proof!.laws.instances).map(([l, inst]) => [l, Object.fromEntries(Object.entries(inst).filter(([n]) => !n.startsWith('?')))]))}}
  expect(checkStepLaws(m, laws, steps, dropped)).toBe(false)
  const droppedSteps = {...r.proof!, instances: Object.fromEntries(Object.entries(r.proof!.instances).filter(([n]) => !n.startsWith('?')))}
  expect(checkStepLaws(m, laws, steps, droppedSteps)).toBe(false)
  // Every step law needs its own trees: without the last one's, the proof no longer checks.
  const lastGoals = new Set(stepLawObligations(m, laws, r.proof!.instances, steps.at(-1)!).map(g => g.name))
  const missing = {...r.proof!, trees: Object.fromEntries(Object.entries(r.proof!.trees).filter(([n]) => !lastGoals.has(n)))}
  expect(checkStepLaws(m, laws, steps, missing)).toBe(false)
  // The goals carry each quantified flag's closing: a witness and the instances.
  const goal = stepLawObligations(m, laws, r.proof!.instances, steps[0]!)[0]!
  expect(JSON.stringify(goal.hyps)).toContain('w?covered')
})

// Fuzz: a set S kept by the machine and a set I the request carries; random writes at every key and quantified flags
// in guards; random laws about every key. Whenever the kernel accepts, no run breaks a law.
test('a set law the kernel accepts holds on every run', () => {
  const v = (name: string): E => ({op: 'var', name}), cc = (value: number): E => ({op: 'const', value}), at = (map: string, key: E): E => ({op: 'get', map, key})
  const cellTerm = (key: E): E => [at('S', key), at('I', key), at('T', key), cc(rand(2))][rand(4)]!
  const cellC = (key: E): C => ({op: rand(2) ? '<=' : '=', a: cellTerm(key), b: cellTerm(key)})
  let proven = 0, broken = 0, refutedRuns = 0, total = 0
  for (let trial = 0; trial < 120; trial++) {
    const guard: C = rand(2) ? {op: 'flag', name: 'q'} : {op: 'not', x: {op: 'flag', name: 'q'}}
    const m: Machine = {name: 'sets', params: [], inputs: ['a'], state: {n: cc(0)}, maps: {S: 0, T: 0}, inputMaps: ['I'],
      step: {flags: {q: {op: 'all', key: 'k', c: cellC(v('k'))}, bits: {op: 'all', key: 'k', c: {op: '<=', a: at('I', v('k')), b: cc(1)}}},
        state: {n: {op: 'if', c: guard, then: {op: 'add', a: v('n'), b: cc(1)}, else: v('n')}},
        maps: {S: {each: 'j', value: {op: 'if', c: guard, then: ([at('I', v('j')), {op: 'max', a: at('S', v('j')), b: at('I', v('j'))}, {op: 'min', a: at('S', v('j')), b: at('T', v('j'))}] as E[])[rand(3)]!, else: at('S', v('j'))}},
          T: {each: 'j', value: rand(2) ? at('T', v('j')) : {op: 'max', a: at('T', v('j')), b: at('S', v('j'))}}}},
      assume: {op: 'flag', name: 'bits'}}
    const law: Law = {name: 'random', forall: 'x', holds: {op: rand(2) ? '<=' : '=', a: [at('S', v('x')), at('T', v('x')), cc(1)][rand(3)]!, b: [at('S', v('x')), at('T', v('x')), cc(1)][rand(3)]!}}
    const r = proveLaws(m, [law])
    total++
    const run = interpret(m)
    let hit = false
    for (let t = 0; t < 60 && !hit; t++) {
      let st = run.init({})
      const on = watch(m, run, law, {}, 3)
      if (!on.start(st)) { hit = true; break }
      for (let i = 0; i < 6 && !hit; i++) {
        const input: Request = {a: 0, I: new Map([0, 1, 2, 3].filter(() => rand(2) === 1).map(key => [key, 1] as const))}
        if (!allowed(m, run, {}, st, input)) continue
        const before = st
        st = run.step({}, st, input)
        if (!on.step(before, input, st)) hit = true
      }
    }
    if (r.proven && r.checked) { proven++; expect(hit, JSON.stringify({step: m.step, law})).toBe(false) }
    else if (hit) refutedRuns++
    if (hit) broken++
  }
  console.log(`sets fuzz: ${total} laws, ${proven} proven (none broken by a run), ${refutedRuns} refused and broken by a run, ${broken} broken in all`)
  expect(proven).toBeGreaterThan(15)
  expect(refutedRuns).toBeGreaterThan(15)
}, 600_000)
