// Cyclic proofs: the kernel's check (kernel/cyclic.ts) accepts what proveCyclic finds and refuses tampered proofs; the
// instances (a recurrence, a machine, a fold) agree with the usual rules; nested and mutual inductions no rule had.
import {expect, test} from 'bun:test'
import type {E} from './machine.ts'
import {type Cyclic, refuseCyclic} from '../kernel/cyclic.ts'
import {foldNodes, machineNodes, proveCyclic, recurNodes} from './cyclic.ts'
import {proveLaws} from '../kernel/prove.ts'
import {mccarthy, mutual} from '../examples/cyclic.ts'
import {counter, counterLaws, growing, retries, retryLaws} from '../examples/lemmas.ts'
import {rollup, rollupLaws} from '../examples/folds.ts'

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
