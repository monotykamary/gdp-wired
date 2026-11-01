// Cyclic proofs: the kernel's check (kernel/cyclic.ts) accepts what proveCyclic finds and refuses tampered proofs; the
// instances (a recurrence, a machine, a fold) agree with the usual rules, and translate their proofs; nested and mutual
// inductions no rule had.
import {expect, test} from 'bun:test'
import type {C, E, Law} from './machine.ts'
import {type CNode, type Cyclic, type Fact, type Use, descentGoal, mainGoal, premiseGoal, refuseCyclic} from '../kernel/cyclic.ts'
import type {Goal, Tree} from '../kernel/kernel.ts'
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

// The guards of kernel/cyclic.ts's refuseCyclic, each with a proof only it refuses (its mutants, kernel/mutants.ts, accept
// each: kernel/MUTANTS.md). The small proofs are grown here: every tree by grow, on the goal the kernel builds.
const v = (name: string): E => ({op: 'var', name}), k = (value: number): E => ({op: 'const', value})
const yes: C = {op: '<=', a: k(0), b: k(0)}
type Spec = Omit<CNode, 'main' | 'uses'> & {uses: Omit<Use, 'premises' | 'descent'>[]}
const tree = (g: Goal): Tree => { const o = grow(g); if (!('tree' in o)) throw new Error(`${g.name}: no tree`); return o.tree }
const build = (facts: Fact[], specs: Spec[], premise = (g: Goal) => tree(g)): Cyclic => ({facts, nodes: specs.map(n => ({...n, main: tree(mainGoal(facts, specs, n)),
  uses: n.uses.map(u => ({...u, premises: specs[u.node]!.hyps.map((c, i) => premise(premiseGoal(facts, n, u, c, i))), descent: tree(descentGoal(facts, n, u, specs[u.node]!))}))}))})

test('a use whose node\'s hypothesis doesn\'t follow is refused (else every x would be at least 1)', () => {
  const x = v('x'), pos: C = {op: '<=', a: k(1), b: x}
  const specs: Spec[] = [{name: 'pos', hyps: [pos], concl: pos, rank: [k(0)], insts: [], uses: []},
    {name: 'every x', hyps: [], concl: pos, rank: [k(1)], insts: [], uses: [{node: 0, subst: {x}, guard: yes}]}]
  // (the premise, 1 <= x at every x, has no tree: the first node's own tree stands in for it)
  const p = build([], specs, () => tree(mainGoal([], specs, specs[0]!)))
  expect(refuseCyclic(p)).toMatch(/hypothesis 0 of pos/)
})

test('a use may not assign a variable a fact reads, whatever the other facts read (else y = 0 from x = 0)', () => {
  const [x, y, z] = ['x', 'y', 'z'].map(v) as [E, E, E]
  const facts: Fact[] = [{name: 'x is 0', keys: [], holds: {op: '=', a: x, b: k(0)}}, {name: 'z', keys: [], holds: {op: '<=', a: k(0), b: z}}]
  const specs: Spec[] = [{name: 'x0', hyps: [], concl: {op: '=', a: x, b: k(0)}, rank: [k(0)], insts: [{fact: 0, at: []}], uses: []},
    {name: 'y0', hyps: [], concl: {op: '=', a: y, b: k(0)}, rank: [k(1)], insts: [], uses: [{node: 0, subst: {x: y}, guard: yes}]}]
  expect(refuseCyclic(build(facts, specs))).toMatch(/assigns a variable a fact reads/)
})

test('a descent read with the tie as ≤ (Lean\'s lexLtC reads it as =) is refused', () => {
  const [x, y, z] = ['x', 'y', 'z'].map(v) as [E, E, E], low: C = {op: '<=', a: k(0), b: x}
  const specs: Spec[] = [{name: 'low', hyps: [], concl: low, rank: [y, x], insts: [], uses: []},
    {name: 'high', hyps: [{op: '=', a: y, b: z}], concl: low, rank: [z, {op: 'add', a: x, b: k(1)}], insts: [], uses: [{node: 0, subst: {x, y}, guard: yes}]}]
  const p = build([], specs)
  expect(refuseCyclic(p)).toBeUndefined()
  const tie = (c: C): C => (c.op === 'and' && c.xs[0]?.op === '=' ? {op: 'and', xs: [{...c.xs[0], op: '<='}, ...c.xs.slice(1).map(tie)]} : c.op === 'or' || c.op === 'and' ? {...c, xs: c.xs.map(tie)} : c.op === 'not' ? {op: 'not', x: tie(c.x)} : c)
  const g = descentGoal([], specs[1]!, specs[1]!.uses[0]!, specs[0]!), le = tree({...g, hyps: g.hyps.map(tie)})
  expect(refuseCyclic({...p, nodes: p.nodes.map((n, i) => (i === 1 ? {...n, uses: [{...n.uses[0]!, descent: le}]} : n))})).toMatch(/doesn't lower the rank/)
})

test('the language: a flag, a quantifier or a key twice in a fact read by no node is refused; a use names a node, its premises one a hypothesis', () => {
  const p = proof(mccarthy()), with_ = (f: Fact): Cyclic => ({...p, facts: [...p.facts, f]})
  expect(refuseCyclic(with_({name: 'a flag', keys: [], holds: {op: 'flag', name: 'f'}}))).toMatch(/a flag or a quantifier/)
  expect(refuseCyclic(with_({name: 'all', keys: [], holds: {op: 'all', key: 'j', c: {op: '<=', a: k(0), b: v('j')}}}))).toMatch(/a flag or a quantifier/)
  expect(refuseCyclic(with_({name: 'twice', keys: ['j', 'j'], holds: {op: '<=', a: k(0), b: v('j')}}))).toMatch(/a key twice/)
  // (two nodes, the second's main goal refuted without its use, which reads the first: 0 <= x at every x)
  const x = v('x'), low: C = {op: '<=', a: k(0), b: x}
  const q = build([], [{name: 'low', hyps: [], concl: low, rank: [k(0)], insts: [], uses: []},
    {name: 'again', hyps: [], concl: low, rank: [k(1)], insts: [], uses: [{node: 0, subst: {x}, guard: yes}]}])
  const use = (f: (u: Use) => Use): Cyclic => ({...q, nodes: q.nodes.map((n, i) => (i === 1 ? {...n, uses: [f(n.uses[0]!)]} : n))})
  expect(refuseCyclic(q)).toBeUndefined()
  expect(refuseCyclic(use(u => ({...u, node: 2})))).toMatch(/names no node/)
  expect(refuseCyclic(use(u => ({...u, premises: [u.descent]})))).toMatch(/1 premise trees for 0 hypotheses/)
})
