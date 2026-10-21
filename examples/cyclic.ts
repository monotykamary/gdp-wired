// Inductions no rule had before, as cyclic proofs (core/cyclic.ts): for the suite (`bun examples/cyclic.ts`),
// core/cyclic.test.ts and lean-kernel/package-check.ts.
//   - McCarthy's 91 function: f(k) = k − 10 above 100, else f(f(k + 11)): nested recursion, which `recur` (a recurrence
//     from x to x + 1) can't define. Every f that meets the equation gives 91 at every n <= 101, by induction on
//     101 − n with three uses of the claim: at n + 11 (whose value is then 91), at 91, and at n + 1. A variant claiming
//     92 is refuted
//   - two functions defined by each other (a(0) = b(0) = 0, a(x + 1) = b(x) + 1, b(x + 1) = a(x) + 2): their bounds
//     a(x) <= 2x and b(x) <= 2x are proven together, each lemma at x using the other at x − 1. `recur` reads only
//     functions defined before; this is a mutual induction
import type {C, E} from '../core/machine.ts'
import {type CyclicVerdict, type NodeSpec, proveCyclic} from '../core/cyclic.ts'
import type {Fact} from '../kernel/cyclic.ts'

const v = (name: string): E => ({op: 'var', name}), k = (value: number): E => ({op: 'const', value})
const add = (a: E, b: E): E => ({op: 'add', a, b}), sub = (a: E, b: E): E => ({op: 'sub', a, b})
const get = (map: string, key: E): E => ({op: 'get', map, key})
const le = (a: E, b: E): C => ({op: '<=', a, b}), lt = (a: E, b: E): C => ({op: '<', a, b}), eq = (a: E, b: E): C => ({op: '=', a, b})
const and = (...xs: C[]): C => ({op: 'and', xs})

export function mccarthy(claim = 91): {facts: Fact[], specs: NodeSpec[]} {
  const n = v('n'), kk = v('k'), f = (key: E) => get('f', key)
  const facts: Fact[] = [{name: 'f(k) = k − 10 above 100, else f(f(k + 11))', keys: ['k'],
    holds: eq(f(kk), {op: 'if', c: lt(k(100), kk), then: sub(kk, k(10)), else: f(f(add(kk, k(11))))})}]
  const specs: NodeSpec[] = [{
    name: `f(n) = ${claim} for n <= 101`, hyps: [le(n, k(101))], concl: eq(f(n), k(claim)), rank: [sub(k(101), n)],
    insts: [{fact: 0, at: [n]}, {fact: 0, at: [add(n, k(11))]}],
    uses: [
      {node: 0, subst: {n: add(n, k(11))}, guard: le(n, k(90))},
      {node: 0, subst: {n: k(91)}, guard: le(n, k(90))},
      {node: 0, subst: {n: add(n, k(1))}, guard: and(le(k(90), n), le(n, k(100)))},
    ],
  }]
  return {facts, specs}
}

export function mutual(): {facts: Fact[], specs: NodeSpec[]} {
  const x = v('x'), kk = v('k'), a = (key: E) => get('a', key), b = (key: E) => get('b', key)
  const facts: Fact[] = [
    {name: 'a(0) = 0, b(0) = 0', keys: [], holds: and(eq(a(k(0)), k(0)), eq(b(k(0)), k(0)))},
    {name: 'a(k + 1) = b(k) + 1, b(k + 1) = a(k) + 2', keys: ['k'], holds: and(eq(a(add(kk, k(1))), add(b(kk), k(1))), eq(b(add(kk, k(1))), add(a(kk), k(2))))},
  ]
  const both = (guard: C) => [0, 1].map(node => ({node, subst: {x: sub(x, k(1))}, guard}))
  const at = [{fact: 0, at: []}, {fact: 1, at: [sub(x, k(1))]}]
  const specs: NodeSpec[] = [
    {name: 'a(x) <= 2x', hyps: [], concl: le(a(x), {op: 'mul', k: 2, a: x}), rank: [x], insts: at, uses: both(le(k(1), x))},
    {name: 'b(x) <= 2x', hyps: [], concl: le(b(x), {op: 'mul', k: 2, a: x}), rank: [x], insts: at, uses: both(le(k(1), x))},
  ]
  return {facts, specs}
}

export const proveExample = (e: {facts: Fact[], specs: NodeSpec[]}): CyclicVerdict => proveCyclic(e.facts, e.specs)

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const [what, e, want] of [['McCarthy 91', mccarthy(), true], ['McCarthy 91 (claims 92)', mccarthy(92), false], ['a and b, by each other', mutual(), true]] as const) {
    const t = performance.now(), out = proveExample(e)
    results.push([`${what} (${Math.round(performance.now() - t)} ms)`, out.proven && out.checked, want])
  }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
