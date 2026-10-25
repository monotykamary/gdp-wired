// Interpolants from the kernel's trees (core/interp.ts) and the searches over them (IMC there, TPA in core/tpa.ts):
// each interpolant is one (A gives it, B refutes it, both by trees the kernel checks), a fixed point is an invariant the
// kernel proves, a run found breaks the law in the interpreter.
import {expect, test} from 'bun:test'
import {parseChc} from '../compare/chc/chc.ts'
import {build, checkDerivation, requestOf, stepsOf} from '../compare/chc/translate.ts'
import {byStep, imc, interpolate, stutter} from './interp.ts'
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
