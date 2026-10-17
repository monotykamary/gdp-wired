// Quantifiers anywhere (core/dsl.ts): a condition at every key written inside a flag, a term, a write or the
// assumption is named as a flag of its own, and one inside a law is pulled out as the law's key. The derived authority
// written that way is proven and its broken variant refused; the named flags agree with the conditions they replace on
// random states; what has no one-key reading (two keys at once) is refused; and some key (a quantifier under a not in a
// law) is proven through a witness the prover finds among a few candidates, or the one the law names.
import {expect, test} from 'bun:test'
import {type C, type Machine, type State, evalC} from './machine.ts'
import {everyKey, nat, rule, someKey, when} from './dsl.ts'
import {inlineAuthority, inlineLaws, inlineSteps, memberLaws, memberSteps, members} from '../examples/quantifiers.ts'
import {proveLaws, proveStepLaws} from '../kernel/prove.ts'

test('quantifiers inside flags, the assumption and laws: named as flags and keys, proven; the broken variant refused', () => {
  const ok = inlineAuthority(), m = ok.machine
  // Only whole flags reach the kernel: each quantifier is a flag of its own, placed before the flags that read it.
  const flags = Object.entries(m.step.flags!)
  expect(flags.filter(([, c]) => c.op === 'all').length).toBe(3)
  for (const [, c] of flags) if (c.op !== 'all') expect(JSON.stringify(c)).not.toContain('"op":"all"')
  expect(JSON.stringify(m.assume)).not.toContain('"op":"all"')
  const ls = inlineLaws(ok)
  expect(ls.map(l => l.forall !== undefined)).toEqual([true, true, true, false])
  expect(proveStepLaws(m, ls, inlineSteps(ok))).toMatchObject({proven: true, checked: true})
  const named = inlineAuthority('checks only the named grant')
  expect(proveStepLaws(named.machine, inlineLaws(named), []).proven).toBe(false)
}, 120_000)

// Random states: a named flag's value (each read in order, as a step decides them) gives each condition the value the
// condition has read directly, with quantifiers over the keys at hand.
test('named flags agree with the conditions they replace', () => {
  let seed = 5
  const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
  const r = rule('shapes').inputs({a: nat}).state({s: 0}).maps({A: 0, B: 0})
    .flags(({a, s, A, B}) => ({
      p: a.atMost(s),
      nested: everyKey(k => A.at(k).atMost(B.at(k)).or(everyKey(j => B.at(j).eq(0)))),
    }))
    .flags(({a, A, B, p}) => ({
      guarded: everyKey(k => p.implies(A.at(k).atMost(a))),
      inside: A.subsetOf(B).and(p.or(everyKey(k => B.at(k).atMost(1)).not())),
    }))
    .step(({s, a, A, inside, guarded, nested}) => ({s: when(everyKey(k => A.at(k).atMost(s)).or(inside), s.plus(a), when(guarded.and(nested), s, 0))}))
  const m = r.machine
  // The conditions as written, quantifiers read directly (evalC reads one anywhere).
  const kEnv = (k: string) => ({op: 'var', name: k}) as const
  const at = (map: string, key: string) => ({op: 'get', map, key: kEnv(key)}) as const
  const le = (a: unknown, b: unknown) => ({op: '<=', a, b}) as C
  const written: Record<string, C> = {
    p: le({op: 'var', name: 'a'}, {op: 'var', name: 's'}),
    nested: {op: 'all', key: 'k', c: {op: 'or', xs: [le(at('A', 'k'), at('B', 'k')), {op: 'all', key: 'j', c: {op: '=', a: at('B', 'j'), b: {op: 'const', value: 0}}}]}},
  }
  written.guarded = {op: 'all', key: 'k', c: {op: 'or', xs: [{op: 'not', x: written.p!}, le(at('A', 'k'), {op: 'var', name: 'a'})]}}
  written.inside = {op: 'and', xs: [{op: 'all', key: 'k', c: le(at('A', 'k'), at('B', 'k'))}, {op: 'or', xs: [written.p!, {op: 'not', x: {op: 'all', key: 'k', c: le(at('B', 'k'), {op: 'const', value: 1})}}]}]}
  const plain: Machine = {...m, step: {}}
  let compared = 0
  for (let t = 0; t < 400; t++) {
    const st: State = {scalars: {s: rand(4)}, maps: {A: new Map(), B: new Map()}}
    for (const key of [0, 1, 2]) { if (rand(2)) st.maps.A!.set(key, rand(3)); if (rand(2)) st.maps.B!.set(key, rand(3)) }
    const env: Record<string, number> = {a: rand(4)}
    for (const [f, c] of Object.entries(m.step.flags!)) env[`?${f}`] = evalC(c, env, st, plain) ? 1 : 0
    for (const [f, c] of Object.entries(written)) { expect(env[`?${f}`], f).toBe(evalC(c, env, st, plain) ? 1 : 0); compared++ }
  }
  expect(compared).toBe(1600)
})

test('what has no one-key reading is refused, by name', () => {
  const r = rule('refusals').state({s: 0}).maps({A: 0, B: 0})
  expect(() => r.flags(({A, B}) => ({two: everyKey(k => everyKey(j => A.at(k).atMost(B.at(j))))})).step(({s}) => ({s})).machine).toThrow(/two keys at once/)
  expect(() => r.law('either all A or all B', ({A, B}) => everyKey(k => A.at(k).eq(0)).or(everyKey(k => B.at(k).eq(0))))).toThrow(/two keys at once/)
  expect(() => r.law('a key beside another', ({A, B}) => ({forall: k => A.at(k).eq(0).or(everyKey(j => B.at(j).eq(0)))}))).toThrow(/two keys at once/)
  // One quantifier beside parts that don't read a key is one key.
  expect(r.law('if s then all A', ({s, A}) => s.eq(1).implies(everyKey(k => A.at(k).eq(0)))).forall).toBeDefined()
})

test('some key: proven through a witness the prover finds, or the one named; refused when none works', () => {
  const ok = members()
  const laws = memberLaws(ok)
  const r = proveLaws(ok.machine, laws)
  expect(r).toMatchObject({proven: true, checked: true})
  expect(r.laws![0]!.holds).toEqual({op: 'or', xs: [{op: 'not', x: {op: '<=', a: {op: 'const', value: 1}, b: {op: 'var', name: 'count'}}}, {op: 'not', x: {op: 'not', x: {op: '=', a: {op: 'get', map: 'S', key: {op: 'var', name: 'last'}}, b: {op: 'const', value: 1}}}}]})
  expect(r.laws![0]!.stated).toEqual(laws[0]!.holds)
  // Named: the same proof.
  expect(proveLaws(ok.machine, [ok.law('named', ({count, last, S}) => count.atLeast(1).implies(someKey(k => S.at(k).eq(1), last)))])).toMatchObject({proven: true, checked: true})
  // A step law: an add puts some name in, and the request's name is one.
  const rs = proveStepLaws(ok.machine, laws, memberSteps(ok))
  expect(rs).toMatchObject({proven: true, checked: true})
  expect(JSON.stringify(rs.stepLaws![0]!.then)).toContain('"key":{"op":"var","name":"name"}')
  // Forgetting the name leaves no candidate that works: refused, naming the law.
  const bad = members('forgets the name')
  const rb = proveLaws(bad.machine, memberLaws(bad))
  expect(rb.proven).toBe(false)
  expect(rb.failed!.stuck).toMatch(/no witness found for some key in something was added/)
})
