// Inductions no rule had before, as cyclic proofs (core/cyclic.ts): for the suite (`bun examples/cyclic.ts`),
// core/cyclic.test.ts and lean-kernel/package-check.ts.
//   - McCarthy's 91 function: f(k) = k − 10 above 100, else f(f(k + 11)): nested recursion, which `recur` (a recurrence
//     from x to x + 1) can't define. Every f that meets the equation gives 91 at every n <= 101, by induction on
//     101 − n with three uses of the claim: at n + 11 (whose value is then 91), at 91, and at n + 1. A variant claiming
//     92 is refuted
//   - two functions defined by each other (a(0) = b(0) = 0, a(x + 1) = b(x) + 1, b(x + 1) = a(x) + 2): their bounds
//     a(x) <= 2x and b(x) <= 2x are proven together, each lemma at x using the other at x − 1. `recur` reads only
//     functions defined before; this is a mutual induction
//   - machines whose laws are proven as cyclic proofs over their runs (machineNodes) and carried back to the machine in
//     Lean (lean-kernel/Bridge.lean's cyc_machine_sound, package-check's cyc* items): a write at every key (fill), a map
//     each request carries (tally), inputs under an assumption and a precondition (budget)
import type {C, E, Law, Machine} from '../core/machine.ts'
import {type CyclicVerdict, type NodeSpec, machineNodes, proveCyclic} from '../core/cyclic.ts'
import type {Fact} from '../kernel/cyclic.ts'
import {forall, min, nat, rule, when} from '../core/dsl.ts'
import {proveLaws} from '../kernel/prove.ts'

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

export const fill = () => rule('fill').params({cap: nat}).inputs({}).maps({Level: 0})
  .step(({Level, cap}) => ({Level: Level.each(k => min(Level.at(k).plus(1), cap))}))
export const fillLaws = (r = fill()): Law[] => [r.law('every level within the cap', ({Level, cap}) => forall(k => Level.at(k).atMost(cap)))]
export const tally = () => rule('tally').params({cap: nat}).inputs({who: nat}).carries('Ok').maps({Count: 0})
  .flags(({who, Ok, Count, cap}) => ({counted: Ok.at(who).eq(1).and(Count.at(who).lt(cap))}))
  .step(({who, counted, Count}) => ({Count: Count.bump(who, counted)}))
export const tallyLaws = (r = tally()): Law[] => [r.law('every count within the cap', ({Count, cap}) => forall(k => Count.at(k).atMost(cap)))]
export const budget = (bug?: 'grants past the cap') => rule('budget').params({cap: nat}).inputs({amt: nat}).state({spent: 0, n: 0})
  .pre(({cap}) => cap.atLeast(1)).assume(({amt}) => amt.atLeast(1))
  .flags(({amt, spent, cap}) => ({ok: bug ? spent.atMost(cap) : spent.plus(amt).atMost(cap)}))
  .step(({amt, ok, spent, n}) => ({spent: when(ok, spent.plus(amt), spent), n: when(ok, n.plus(1), n)}))
export const budgetLaws = (r = budget()): Law[] => [r.law('spent within the cap', ({spent, cap}) => spent.atMost(cap)),
  r.law('each grant spends one or more', ({spent, n}) => n.atMost(spent))]
// A machine's laws as one cyclic proof over its runs, the laws' keys as the usual proof names them.
export const machineProof = (m: Machine, laws: Law[]): CyclicVerdict => {
  const {facts, specs} = machineNodes(m, laws, proveLaws(m, laws).proof?.instances ?? {})
  return proveCyclic(facts, specs)
}

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const [what, e, want] of [['McCarthy 91', mccarthy(), true], ['McCarthy 91 (claims 92)', mccarthy(92), false], ['a and b, by each other', mutual(), true]] as const) {
    const t = performance.now(), out = proveExample(e)
    results.push([`${what} (${Math.round(performance.now() - t)} ms)`, out.proven && out.checked, want])
  }
  for (const [what, m, laws, want] of [['fill', fill().machine, fillLaws(), true], ['tally', tally().machine, tallyLaws(), true], ['budget', budget().machine, budgetLaws(), true],
    ['budget (grants past the cap)', budget('grants past the cap').machine, budgetLaws(budget('grants past the cap')), false]] as const) {
    const t = performance.now(), out = machineProof(m, laws)
    results.push([`${what}, over its runs (${Math.round(performance.now() - t)} ms)`, out.proven && out.checked, want])
  }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
