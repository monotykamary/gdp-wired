// Interpolants from the kernel's trees (core/interp.ts) and the searches over them (IMC there, TPA in core/tpa.ts):
// each interpolant is one (A gives it, B refutes it, both by trees the kernel checks), a fixed point is an invariant the
// kernel proves, a run found breaks the law in the interpreter.
import {expect, test} from 'bun:test'
import {parseChc} from '../compare/chc/chc.ts'
import {build, checkDerivation, requestOf, stepsOf} from '../compare/chc/translate.ts'
import {byStep, fromDag, fromTree, imc, interpolate, stutter} from './interp.ts'
import {compose, expand, liftProven} from '../compare/chc/compose.ts'
import {boundedSearch} from './bmc.ts'
import {type Refuted, growCdcl} from '../kernel/cdcl.ts'
import {tpa} from './tpa.ts'
import {relax} from './bmc.ts'
import {proveRule} from './dsl.ts'
import type {C, E} from './machine.ts'
import {check, stepLawObligations, substC} from '../kernel/kernel.ts'
import {counted, grow} from '../kernel/prove.ts'

// Two counters stepped together from 0: x = y always (safe); x reaches 5 (unsafe, a run of 7 steps).
const safe = `(declare-fun inv (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 0)) (inv x y))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int)) (=> (and (inv x y) (= x1 (+ x 1)) (= y1 (+ y 1))) (inv x1 y1))))
(assert (forall ((x Int) (y Int)) (=> (and (inv x y) (not (= x y))) false)))`
const unsafe = safe.replace('(not (= x y))', '(>= x 5)')
const refuted = (hyps: C[]) => { const g = {name: 'refuted', hyps}, out = grow(g, new Map(), {nodes: 0, until: Infinity}); return 'tree' in out && check(g, out.tree) }

test('each cut of a bounded refutation: A gives its interpolant, B refutes it', () => {
  const b = build(parseChc(safe)), m = b.rule.machine, names = Object.keys(m.state), m2 = stutter(m, b.law)
  const then = substC(b.law.holds, {vars: Object.fromEntries(names.map(n => [n, {op: 'var', name: `${n}'`} as E])), maps: {}, flags: {}})
  const start: C = {op: 'and', xs: Object.entries(m.state).map(([n, e]): C => ({op: '=', a: {op: 'var', name: n}, b: e}))}
  const g = stepLawObligations(m2, [], {}, {name: 'cuts', when: start, then, steps: 3})[0]!
  const hyps = relax(g.hyps) ?? g.hyps, st = byStep(m2, hyps)
  for (const j of [1, 2]) {
    const A = hyps.filter((_, i) => st[i]! <= j), B = hyps.filter((_, i) => st[i]! > j)
    const out = interpolate(A, B, names.map(n => `${n}~${j}`), {until: Infinity})
    expect('itp' in out).toBe(true)
    if (!('itp' in out)) continue
    expect(refuted([...A, {op: 'not', x: out.itp}])).toBe(true)
    expect(refuted([...B, out.itp])).toBe(true)
  }
}, 60_000)

test('IMC: the fixed point is an invariant the kernel proves; a run past the start breaks the law', () => {
  const s = build(parseChc(safe)), u = build(parseChc(unsafe))
  const fixed = counted(250, () => imc(s.rule.machine, s.law, {until: Infinity, wall: performance.now() + 30_000}), true)
  expect('inv' in fixed).toBe(true)
  if ('inv' in fixed) { const v = proveRule(s.rule, [s.law, {name: 'imc', holds: fixed.inv}], {search: false}); expect(v.proven && v.checked).toBe(true) }
  const run = counted(250, () => imc(u.rule.machine, u.law, {until: Infinity, wall: performance.now() + 30_000}), true)
  expect('run' in run).toBe(true)
  if ('run' in run) expect(checkDerivation(u, parseChc(unsafe), stepsOf(u, run.run.trace.map(t => requestOf(u, t as Record<string, unknown>))))).toBeUndefined()
}, 120_000)

test('TPA: a run of 7 steps at the third level, confirmed against the CHC', () => {
  const u = build(parseChc(unsafe))
  const out = counted(250, () => tpa(u.rule.machine, u.law, {until: Infinity, wall: performance.now() + 30_000, kinds: u.rule.kindLaws().map(l => l.holds)}), true)
  expect('run' in out && out.level).toBe(2)
  if ('run' in out) expect(checkDerivation(u, parseChc(unsafe), stepsOf(u, out.run.trace.map(t => requestOf(u, t as Record<string, unknown>))))).toBeUndefined()
}, 60_000)

test('the same cut read off CDCL\'s DAG and off its unfolded tree: each an interpolant', () => {
  const b = build(parseChc(safe)), m = b.rule.machine, names = Object.keys(m.state), m2 = stutter(m, b.law)
  const then = substC(b.law.holds, {vars: Object.fromEntries(names.map(n => [n, {op: 'var', name: `${n}'`} as E])), maps: {}, flags: {}})
  const start: C = {op: 'and', xs: Object.entries(m.state).map(([n, e]): C => ({op: '=', a: {op: 'var', name: n}, b: e}))}
  const g = stepLawObligations(m2, [], {}, {name: 'cuts', when: start, then, steps: 4})[0]!
  const hyps = g.hyps, st = byStep(m2, hyps)
  for (const j of [1, 2, 3]) {
    const goal = {name: 'cut', hyps}, isA = (i: number) => st[i]! <= j, A = hyps.filter((_, i) => isA(i)), B = hyps.filter((_, i) => !isA(i))
    const d = growCdcl(goal, new Map(), {nodes: 0, until: Infinity}, {model: true, dag: true}) as Refuted
    const t = growCdcl(goal, new Map(), {nodes: 0, until: Infinity})
    expect(d.dag).toBeDefined()
    expect('tree' in t).toBe(true)
    for (const itp of [fromDag(goal, d.dag!, isA), 'tree' in t ? fromTree(goal, t.tree, isA) : undefined]) {
      expect(itp).toBeDefined()
      expect(refuted([...A, {op: 'not', x: itp!}])).toBe(true)
      expect(refuted([...B, itp!])).toBe(true)
    }
  }
}, 60_000)

// A loop between two chains: x counts to n by a chain of three predicates, y follows it by a chain of two.
const chain = `(declare-fun a (Int Int Int) Bool) (declare-fun b (Int Int Int) Bool) (declare-fun c (Int Int Int) Bool)
(declare-fun d (Int Int Int) Bool) (declare-fun e (Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (n Int)) (=> (and (= x 0) (= y 0) (>= n 0)) (a x y n))))
(assert (forall ((x Int) (y Int) (n Int)) (=> (and (a x y n) (< x n)) (b x y n))))
(assert (forall ((x Int) (y Int) (n Int) (x1 Int)) (=> (and (b x y n) (= x1 (+ x 1))) (c x1 y n))))
(assert (forall ((x Int) (y Int) (n Int) (y1 Int)) (=> (and (c x y n) (= y1 (+ y 1))) (d x y1 n))))
(assert (forall ((x Int) (y Int) (n Int)) (=> (d x y n) (a x y n))))
(assert (forall ((x Int) (y Int) (n Int)) (=> (and (a x y n) (>= x n)) (e x y n))))
(assert (forall ((x Int) (y Int) (n Int)) (=> (and (e x y n) (not (= x y))) false)))`
const chainBad = chain.replace('(= y1 (+ y 1))', '(= y1 (+ y 2))')

test('chains composed: the loop alone is left; a sat answer lifted and proven of the original rule, an unsat run expanded and checked against the original CHC', () => {
  const chc = parseChc(chain), cc = compose(chc), bo = build(chc), bc = build(cc.chc)
  expect(cc.eliminated.length).toBe(4)
  expect(cc.chc.clauses.length).toBe(3)
  const fixed = counted(250, () => imc(bc.rule.machine, bc.law, {until: Infinity, wall: performance.now() + 30_000}), true)
  expect('inv' in fixed).toBe(true)
  if ('inv' in fixed) expect(liftProven(cc, bo, {op: 'and', xs: [bc.law.holds, fixed.inv]}, performance.now() + 30_000).proven).toBe(true)
  // a law the composed rule's invariant doesn't give: lifted, it isn't proven
  const bad = parseChc(chainBad), cb = compose(bad), ob = build(bad), rb = build(cb.chc)
  const out = boundedSearch(rb.rule.machine, [rb.law], {forcedMs: 1000})!.run(30_000, performance.now() + 30_000)
  expect(typeof out).toBe('object')
  if (typeof out === 'object') {
    const raws = expand(ob, rb, cb, stepsOf(rb, out.trace.map(t => requestOf(rb, t as Record<string, unknown>))))
    expect(typeof raws).not.toBe('string')
    if (typeof raws !== 'string') { expect(raws.length).toBeGreaterThan(out.trace.length); expect(checkDerivation(ob, bad, stepsOf(ob, raws))).toBeUndefined() }
  }
  expect(liftProven(cb, ob, rb.law.holds, performance.now() + 10_000).proven).toBe(false)
}, 120_000)
