import {expect, test} from 'bun:test'
import {type C, type Compiled, type E, type Law, type Machine, type State, compileC, compileFunction, compileJs, evalC, fastStep, hasFinite, interpret, loadJs, n, x, get, times, same, less} from './machine.ts'
import {finiteBound, scope} from '../kernel/kernel.ts'
import {exists, lit, nat, rule, sizedSort, when} from './dsl.ts'
import {holdsAt} from './exists.ts'
import {watch} from './watch.ts'
import {runtimeWall} from './runtime-wall.ts'
import {finiteEvaluator} from './finite-houdini.ts'
import {tinyFiniteCandidates} from './finite-tiny.ts'
import {proveLaws} from '../kernel/prove.ts'
import {requestQuotient} from './request-quotient.ts'
import {domainStep} from './infer.ts'
import {bmcFits} from './bmc.ts'
import {encC} from '../interchange/format.ts'
import {fitsU32} from '../research/search/compile.ts'
import {product} from './compose.ts'
import {substC} from '../kernel/kernel.ts'

const q = (body: C, size: E = x('size')): Extract<C, {op: 'all'}> => ({op: 'all', key: 'k', finite: 'Item', c: {op: 'or', xs: [{op: 'not', x: less(x('k'), size)}, body]}})
const machine = (flag: C): Machine => ({name: 'finite-test', params: ['size'], inputs: [], state: {s: n(1)}, maps: {A: 0}, step: {flags: {all: flag}, state: {s: {op: 'if', c: {op: 'flag', name: 'all'}, then: n(1), else: n(0)}}}})
const empty = (): State => ({scalars: {s: 1}, maps: {A: new Map()}})

// A function read has no finite support. Its only false point is NOT a legacy
// breakpoint: the old enumerator sees the bound and its neighbours, not key 17.
test('finite enumeration catches a false non-breakpoint, at every CPU entry', () => {
  const flag = q(same(get('F', times(2, x('k'))), n(0)))
  const m: Machine = {...machine(flag), fns: {F: {js: 'k => k === 34 ? 1 : 0'}}}
  scope(m)
  const st = empty(), params = {size: 100}
  expect(evalC(flag, params, st, m)).toBe(false)
  expect(compileC(flag, m)(params, st)).toBe(false)
  const mutant = {...flag}; delete mutant.finite
  expect(evalC(mutant, params, st, m)).toBe(true) // demonstrates the broken breakpoint evaluator
  const rt = interpret(m), js = loadJs(m)
  expect(rt.step(params, rt.init(params), {}).scalars.s).toBe(0)
  expect(js.step(params, js.init(params), {}).scalars.s).toBe(0)
  expect(fastStep(m)).toBeUndefined()
  const json = JSON.parse(JSON.stringify(m)) as Machine
  expect(evalC(json.step.flags!.all!, params, st, json)).toBe(false)
})

test('zero, singleton and more than 64 elements, arbitrary repeated/tuple key reads', () => {
  const r = rule('finite-builder').params({size: nat}).state({s: 1}).maps({A: 0})
    .flags(({size, A}) => ({p: sizedSort('Item', size).every(k => A.at(k.times(2).plus(k)).eq(0))}))
    .step(({p}) => ({s: when(p, 1, 0)}))
  const m = r.machine
  expect(hasFinite(m)).toBe(true)
  for (const size of [0, 1, 65, 129]) {
    const rt = interpret(m), st = rt.init({size})
    st.maps.A!.set(3 * 64, 1)
    expect(rt.step({size}, st, {}).scalars.s).toBe(size <= 64 ? 1 : 0)
  }
  const tupleFlag = q(same(get('A', {op: 'tup', a: x('k'), b: times(2, x('k'))}), n(0)))
  const tupleM = machine(tupleFlag)
  scope(tupleM)
  expect(evalC(tupleFlag, {size: 100}, empty(), tupleM)).toBe(true)
  expect(loadJs(tupleM).step({size: 100}, empty(), {}).scalars.s).toBe(1)
})

test('bounded existential polarity and empty sorts', () => {
  const some = sizedSort('Item', 0).some(k => k.eq(0))
  const all = sizedSort('Item', 0).every(k => k.eq(0))
  expect(some.ok).toBe(false)
  expect(all.ok).toBe(true)
  expect(evalC(some.c, {}, empty(), machine(all.c))).toBe(false)
  expect(evalC(sizedSort('Item', 65).some(k => k.eq(64)).c, {}, empty(), machine(all.c))).toBe(true)
})

test('a prenexed finite law enumerates its own size, never the sampling bound', () => {
  const r = rule('finite-law').params({size: nat}).state({s: 0}).maps({A: 0}).step(() => ({}))
  const law = r.law('all indexed values zero', ({size, A}) => sizedSort('Item', size).every(k => A.at(k.times(2)).eq(0)))
  const m = r.machine, st = empty(); st.maps.A!.set(34, 1)
  scope(m, [law])
  expect(law.finite).toBe('Item')
  expect(holdsAt(m, law, {size: 100}, st, 4)).toBe(false)
  expect(watch(m, interpret(m), law, {size: 100}, 4).start(st)).toBe(false)
  expect(finiteEvaluator(m)(law, {size: 100}, st)).toBeUndefined()
  const tiny = tinyFiniteCandidates(m, m, [law], {size: 100}, () => { throw new Error('must not screen') })
  expect(tiny.completed).toBe(false)
  expect(tiny.unsupported.join()).toContain('finite sort')
})

test('scope refuses every malformed marker and every mutable bound', () => {
  const good = q(same(x('k'), x('k')))
  const body = good.c as Extract<C, {op: 'or'}>
  const guard = body.xs[0] as Extract<C, {op: 'not'}>
  const cases: C[] = [
    {...good, c: same(x('k'), x('k'))},
    {...good, c: {op: 'or', xs: [{op: 'not', x: {op: '<=', a: x('k'), b: x('size')}}, body.xs[1]!]}},
    {...good, c: {op: 'or', xs: [{op: 'not', x: less(x('other'), x('size'))}, body.xs[1]!]}},
    q(body.xs[1]!, x('k')), q(body.xs[1]!, x('s')), q(body.xs[1]!, x('request')),
    q(body.xs[1]!, get('A', n(0))), {...good, keys: ['other']},
  ]
  for (const c of cases) expect(() => scope({...machine(c), inputs: ['request']})).toThrow()
  const written = machine(good)
  written.step.maps = {A: {each: 'j', value: n(0), finite: 'Item'} as never}
  expect(() => scope(written)).toThrow(/finite marker/)
  const unmarked = {...good}; delete unmarked.finite
  const unrestricted = machine({...unmarked, c: q(same(get('A', times(2, x('k'))), n(0))).c})
  expect(() => scope(unrestricted)).toThrow(/key/)
  expect(finiteBound(good)).toEqual(x('size'))
  expect(guard.x.op).toBe('<')
  expect(() => scope(machine(good), [{name: 'bad metadata', forall: 'k', finite: 'Item', some: ['w'], holds: good.c}])).toThrow()
  expect(() => sizedSort('Item', lit(Number.MAX_SAFE_INTEGER).plus(1)).every(k => k.eq(k))).toThrow()
  expect(() => sizedSort('Item', 3).every(k => exists(w => w.eq(k)))).toThrow(/unquantified/)
  expect(() => sizedSort('Item', 3).every(k => sizedSort('Other', 2).every(j => j.eq(k)))).toThrow(/unquantified/)
})

test('unsupported optimizers refuse instead of merging or sampling finite bodies', () => {
  const m = {...machine(q(same(get('A', times(2, x('k'))), n(0)))), inputs: ['request']}
  const law: Law = {name: 'scalar', holds: same(x('s'), n(1))}
  expect(requestQuotient(m, [{request: 0}, {request: 1}])).toBeUndefined()
  expect(domainStep(m)).toBeUndefined()
  expect(bmcFits(m, [law])).toBe(false)
  expect(() => encC(m.step.flags!.all!)).toThrow(/finite sort/)
  expect(() => fitsU32(m, law, {depth: 1, bound: 2})).toThrow(/finite sort/)
})

test('unsafe finite sizes never round into a successful enumeration', () => {
  const flag = q(same(x('k'), x('k'))), m = machine(flag)
  for (const size of [-1, 0.5, Infinity, Number.MAX_SAFE_INTEGER + 1]) {
    expect(() => evalC(flag, {size}, empty(), m)).toThrow()
    expect(() => loadJs(m).step({size}, empty(), {})).toThrow()
  }
})

test('renaming and substitution preserve and revalidate the finite marker', () => {
  const m = machine(q(same(get('A', times(2, x('k'))), n(0))))
  const both = product(m, m)
  scope(both)
  expect(both.step.flags!.a_all!.op).toBe('all')
  expect(hasFinite(both)).toBe(true)
  expect(interpret(both).step({size: 100}, interpret(both).init({size: 100}), {}).scalars.a_s).toBe(1)
  const renamed = substC(m.step.flags!.all!, {vars: {size: x('length')}, maps: {}, flags: {}})
  scope({...machine(renamed), params: ['length']})
  expect(finiteBound(renamed as Extract<C, {op: 'all'}>)).toEqual(x('length'))
  expect(evalC(renamed, {length: 65}, empty(), machine(renamed))).toBe(true)
})

test('standalone generated finite runtime requires a cooperative callback', () => {
  const m = machine(q(same(x('k'), x('k'))))
  const raw = compileFunction<() => Compiled>([], compileJs(m).replace(/^export function/gm, 'function') + '\nreturn {init, fork, step}')()
  expect(() => raw.step({size: 0}, empty(), {})).toThrow(/cancellation callback/)
  let calls = 0
  expect(raw.step({size: 600}, empty(), {}, () => { calls++ }).scalars.s).toBe(1)
  expect(calls).toBe(4) // entry, 0, 256, 512
  expect(() => raw.step({size: 600}, empty(), {}, () => { throw new Error('stop') })).toThrow('stop')
})

test('finite cancellation fails closed even at size zero', () => {
  const m = machine(q(same(x('k'), x('k')))), old = runtimeWall.check
  runtimeWall.check = () => { throw new Error('cancelled finite enumeration') }
  try {
    for (const size of [0, 100]) {
      expect(() => evalC(m.step.flags!.all!, {size}, empty(), m)).toThrow('cancelled')
      expect(() => loadJs(m).step({size}, empty(), {})).toThrow('cancelled')
    }
  } finally { runtimeWall.check = old }
})

test('guarded closing proves universal bounds, and refuses a false invariant', () => {
  const good = machine(q(less(x('k'), x('size'))))
  const law: Law = {name: 'all remain true', holds: same(x('s'), n(1))}
  expect(proveLaws(good, [law])).toMatchObject({proven: true, checked: true})
  const bad = {...machine(q(same(x('k'), n(0)))), pre: same(x('size'), n(2))}
  expect(proveLaws(bad, [law]).proven).toBe(false)
}, 30_000)
