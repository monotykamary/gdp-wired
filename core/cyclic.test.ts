// Cyclic proofs: the kernel's check (kernel/cyclic.ts) accepts what proveCyclic finds and refuses tampered proofs; the
// instances (a recurrence, a machine, a fold) agree with the usual rules, and translate their proofs; nested and mutual
// inductions no rule had.
import {expect, test} from 'bun:test'
import type {E, Law} from './machine.ts'
import {type Cyclic, refuseCyclic} from '../kernel/cyclic.ts'
import {foldNodes, loopNodes, machineNodes, proveCyclic, recurNodes} from './cyclic.ts'
import {grow, proveLaws} from '../kernel/prove.ts'
import {foldObligations, loopObligations} from '../kernel/kernel.ts'
import {mccarthy, mutual} from '../examples/cyclic.ts'
import {counter, counterLaws, growing, retries, retryLaws} from '../examples/lemmas.ts'
import {rollup, rollupLaws} from '../examples/folds.ts'
import {euclid} from '../examples/cycles.ts'

const proof = (e: ReturnType<typeof mccarthy>): Cyclic => { const r = proveCyclic(e.facts, e.specs); if (!r.proven || !r.checked) throw new Error('not proven'); return r.proof }
const n: E = {op: 'var', name: 'n'}

test('nested and mutual inductions are proven; a false claim is not', () => {
  expect(refuseCyclic(proof(mccarthy()))).toBeUndefined()
  expect(refuseCyclic(proof(mutual()))).toBeUndefined()
  const wrong = proveCyclic(mccarthy(92).facts, mccarthy(92).specs)
  expect(wrong.proven && wrong.checked).toBe(false)
})

test('a back-edge that doesn\'t lower the rank, reads the wrong terms, or leaves a node unranked is refused', () => {
  const p = proof(mccarthy())
  const use0 = (subst: Record<string, E>): Cyclic => ({...p, nodes: p.nodes.map(x => ({...x, uses: x.uses.map((u, j) => (j === 0 ? {...u, subst} : u))}))})
  expect(refuseCyclic(use0({n}))).toMatch(/rank|goal|hypothesis/)
  expect(refuseCyclic(use0({n: {op: 'add', a: n, b: {op: 'const', value: 12}}}))).toBeDefined()
  expect(refuseCyclic({...p, nodes: p.nodes.map(x => ({...x, rank: []}))})).toMatch(/rank/)
  // Two nodes, one unranked: their ranks can't be compared.
  const m = proof(mutual())
  expect(refuseCyclic({...m, nodes: m.nodes.map((x, i) => (i === 1 ? {...x, rank: []} : x))})).toMatch(/different lengths/)
  // A substitution may not assign a variable a fact reads (its keys aside).
  const f = {...p, facts: [{...p.facts[0]!, keys: []}]}
  expect(refuseCyclic(f)).toBeDefined()
})

test('today\'s rules as instances: a recurrence, a machine, a fold, each with the usual verdict', () => {
  const rc = growing().recur!
  const r = recurNodes({name: 'growing', args: rc.args, zero: rc.zero, next: rc.next, lemmas: rc.lemmas, between: rc.between, facts: []})
  const rv = proveCyclic(r.facts, r.specs)
  expect(rv.proven && rv.checked).toBe(true)
  const c = counter(), cl = counterLaws(c), cp = proveLaws(c.machine, cl)
  const mn = machineNodes(c.machine, cl, cp.proof!.instances), mv = proveCyclic(mn.facts, mn.specs)
  expect([cp.proven, mv.proven && mv.checked]).toEqual([true, true])
  // A law that isn't inductive alone: refused both ways.
  const rr = retries('states no lemma'), rl = retryLaws(rr), rp = proveLaws(rr.machine, rl)
  const rn = machineNodes(rr.machine, rl, rp.proof?.instances ?? {}), rnv = proveCyclic(rn.facts, rn.specs)
  expect([rp.proven, rnv.proven && rnv.checked]).toEqual([false, false])
  for (const bug of [undefined, 'caps the leaves only'] as const) {
    const f = rollup(bug), fn = foldNodes(f.fold, rollupLaws(f)), fv = proveCyclic(fn.facts, fn.specs)
    expect(fv.proven && fv.checked).toBe(!bug)
  }
})

test('the usual proofs translated: a machine, a fold and a recurrence, each checked by the kernel', () => {
  const c = counter(), cl = counterLaws(c), cp = proveLaws(c.machine, cl)
  const mn = machineNodes(c.machine, cl, cp.proof!.instances, cp.proof!)
  expect(mn.why).toBeUndefined()
  // (the after-step and start nodes' trees are the usual ones translated, none grown)
  expect(mn.specs.slice(cl.length).every(sp => sp.main)).toBe(true)
  const mv = proveCyclic(mn.facts, mn.specs)
  expect([mv.proven && mv.checked, mv.proven && refuseCyclic(mv.proof)]).toEqual([true, undefined])
  const f = rollup(), fl = rollupLaws(f), goals = foldObligations(f.fold, fl), trees = Object.fromEntries(goals.map(g => { const o = grow(g); return [g.name, 'tree' in o ? o.tree : undefined] }))
  const fn = foldNodes(f.fold, fl, trees as never), fv = proveCyclic(fn.facts, fn.specs)
  expect(fv.proven && fv.checked).toBe(true)
  const rc = growing().recur!, pl = rc.proofs!.lemmas!, lp = proveLaws(pl.machine, pl.laws), lemmas = {m: pl.machine, laws: pl.laws, proof: lp.proof!}
  const rn = recurNodes({name: 'growing', args: rc.args, zero: rc.zero, next: rc.next, lemmas: rc.lemmas, between: [], facts: []}, {lemmas})
  expect(rn.why).toBeUndefined()
  const rv = proveCyclic(rn.facts, rn.specs)
  expect(rv.proven && rv.checked).toBe(true)
})

test('a loop\'s halting translated: its laws and its liveness\'s step laws one cyclic proof, a tampered one refused', () => {
  // gcd by subtraction, ranked a + b with both positive (examples/cycles.ts): the usual trees, then their translation.
  const l = euclid().loop, a: E = {op: 'var', name: 'a'}, b: E = {op: 'var', name: 'b'}, rank: E[] = [{op: 'add', a, b}]
  const laws: Law[] = [{name: 'both positive', holds: {op: 'and', xs: [{op: '<=', a: {op: 'const', value: 1}, b: a}, {op: '<=', a: {op: 'const', value: 1}, b}]}}]
  const goals = loopObligations(l, laws, rank), trees = Object.fromEntries(goals.map(g => { const o = grow(g); if (!('tree' in o)) throw new Error(g.name); return [g.name, o.tree] }))
  const ln = loopNodes(l, laws, rank, trees)
  expect(ln.why).toBeUndefined()
  const lv = proveCyclic(ln.facts, ln.specs)
  if (!lv.proven) throw new Error(`${lv.goal}: ${lv.stuck}`)
  expect([lv.checked, refuseCyclic(lv.proof)]).toEqual([true, undefined])
  // Its last node, the helpful turn's step law: `then` with a false part, a rank no use can drop below, or no use of
  // the turn's node it reads its conclusion from.
  const p = lv.proof, last = p.nodes.length - 1, at = (f: (n: Cyclic['nodes'][number]) => Cyclic['nodes'][number]): Cyclic => ({...p, nodes: p.nodes.map((x, i) => (i === last ? f(x) : x))})
  const zero: E = {op: 'const', value: 0}
  expect(refuseCyclic(at(x => ({...x, concl: {op: 'and', xs: [x.concl, {op: '<', a: zero, b: zero}]}})))).toMatch(/its goal/)
  expect(refuseCyclic(at(x => ({...x, rank: x.rank.map(() => zero)})))).toMatch(/rank/)
  expect(refuseCyclic(at(x => ({...x, uses: []})))).toMatch(/its goal/)
  // A rank that doesn't drop has no usual trees to translate, and none is made.
  expect(loopObligations(l, laws, [a]).every(g => 'tree' in grow(g))).toBe(false)
})
