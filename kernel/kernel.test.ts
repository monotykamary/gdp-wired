// Soundness by brute force: random hypotheses (ifs, mins, maxes, truncation, products, map reads); whenever the kernel
// accepts a refutation, no concrete model (x, y, z in 0..3, the map M any function from 0..3 to 0..3, 0 elsewhere)
// may satisfy them. Also: every proof the kernel accepts stops being accepted when its derivations are emptied.
import {expect, test} from 'bun:test'
import type {C, E} from '../core/machine.ts'
import {type Goal, check, leafConstraints, withProducts} from './kernel.ts'
import {solve} from '../core/solver.ts'
import {grow} from './prove.ts'

// FUZZ_SEED and FUZZ_SCALE shard the fuzz (modal/fuzz.json runs many seeds in parallel); slow goals are reported.
let seed = Number(process.env.FUZZ_SEED ?? 12345)
const scale = Number(process.env.FUZZ_SCALE ?? 1)
const timed = <T>(what: string, goal: unknown, f: () => T): T => { if (process.env.FUZZ_TRACE) require("node:fs").writeFileSync(process.env.FUZZ_TRACE, JSON.stringify(goal)); const t0 = performance.now(), r = f(), ms = performance.now() - t0; if (ms > 2000) console.log(`SLOW ${Math.round(ms)} ms ${what}: ${JSON.stringify(goal)}`); return r }
const rand = (n: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * n) } // high bits: the low ones of this generator barely change
const term = (d: number): E => {
  const r = rand(d <= 0 ? 2 : 10)
  if (r === 0) return {op: 'var', name: ['x', 'y', 'z'][rand(3)]!}
  if (r === 1) return {op: 'const', value: rand(4)}
  if (r === 2) return {op: 'add', a: term(d - 1), b: term(d - 1)}
  if (r === 3) return {op: 'sub', a: term(d - 1), b: term(d - 1)}
  if (r === 4) return {op: 'min', a: term(d - 1), b: term(d - 1)}
  if (r === 5) return {op: 'max', a: term(d - 1), b: term(d - 1)}
  if (r === 6) return {op: 'if', c: cmp(d - 1), then: term(d - 1), else: term(d - 1)}
  if (r === 7) return {op: 'get', map: 'M', key: term(d - 1)}
  if (r === 8) return {op: 'mul', k: 2, a: term(d - 1)}
  return {op: 'prod', a: {op: 'var', name: ['x', 'y'][rand(2)]!}, b: term(0)}
}
const cmp = (d: number): C => {
  const r = rand(5)
  if (r === 3) return {op: 'not', x: cmp(d)}
  if (r === 4 && d > 0) return {op: rand(2) ? 'and' : 'or', xs: [cmp(d - 1), cmp(d - 1)]}
  return {op: (['<', '<=', '='] as const)[rand(3)]!, a: term(d), b: term(d)}
}
type Env = {x: number, y: number, z: number, M: number[]}
const ev = (e: E, env: Env): number => {
  switch (e.op) {
    case 'var': return env[e.name as 'x']
    case 'const': return e.value
    case 'add': return ev(e.a, env) + ev(e.b, env)
    case 'sub': return Math.max(0, ev(e.a, env) - ev(e.b, env))
    case 'min': return Math.min(ev(e.a, env), ev(e.b, env))
    case 'max': return Math.max(ev(e.a, env), ev(e.b, env))
    case 'mul': return e.k * ev(e.a, env)
    case 'prod': return ev(e.a, env) * ev(e.b, env)
    case 'if': return evC(e.c, env) ? ev(e.then, env) : ev(e.else, env)
    case 'get': return env.M[ev(e.key, env)] ?? 0
  }
}
const evC = (c: C, env: Env): boolean => c.op === 'not' ? !evC(c.x, env) : c.op === 'and' ? c.xs.every(y => evC(y, env)) : c.op === 'or' ? c.xs.some(y => evC(y, env))
  : c.op === 'flag' ? false : c.op === '<' ? ev(c.a, env) < ev(c.b, env) : c.op === '<=' ? ev(c.a, env) <= ev(c.b, env) : ev(c.a, env) === ev(c.b, env)
const models = function* (): Generator<Env> {
  for (let m = 0; m < 256; m++) { const M = [m & 3, (m >> 2) & 3, (m >> 4) & 3, (m >> 6) & 3]
    for (let x = 0; x < 4; x++) for (let y = 0; y < 4; y++) for (let z = 0; z < 4; z++) yield {x, y, z, M} }
}

test('the kernel never accepts a refutation of something with a model', () => {
  let accepted = 0, total = 0, stuck = 0; const noSmall: string[] = []
  for (let t = 0; t < 600 * scale; t++) {
    const goal: Goal = {name: 'random', hyps: [cmp(2), cmp(2), cmp(1)]}
    total++
    const out = timed('linear', goal, () => grow(goal))
    if (!("tree" in out)) { stuck++; if (!JSON.stringify(goal).includes('"prod"') && ![...models()].some(env => goal.hyps.every(h => evC(h, env)))) noSmall.push(out.stuck); continue }
    if (!check(goal, out.tree)) continue
    accepted++
    for (const env of models()) if (goal.hyps.every(h => evC(h, env))) throw new Error(`UNSOUND: ${JSON.stringify(goal)} holds at ${JSON.stringify(env)}`)
    const emptied = structuredClone(out.tree); const strip = (n: any): unknown => ('leaf' in n ? (n.leaf = []) : (strip(n.yes), strip(n.no))); strip(emptied)
    expect(check(goal, emptied)).toBe(false)
  }
  console.log(`${accepted} refutations accepted and confirmed by brute force, ${stuck} with a candidate model (${noSmall.length} of them with no model in the small range), of ${total}`)
  expect(accepted).toBeGreaterThan(50 * scale)
  expect(noSmall.filter(why => why === 'unknown')).toEqual([]) // every linear goal left open has an integer witness
}, 600000)

// Higher degrees: monotone polynomials up to degree three (a·v + b·v·w + c·v·v·w, w another natural), true and false
// variants, through the prover and through leaves given random products, including products of earlier product rows.
// Whatever the kernel accepts must have no model.
const mono = (v: E, w: E, [a, b, c]: number[]): E => {
  const vw: E = {op: 'prod', a: v, b: w}
  return {op: 'add', a: {op: 'add', a: {op: 'mul', k: a!, a: v}, b: {op: 'mul', k: b!, a: vw}}, b: {op: 'mul', k: c!, a: {op: 'prod', a: v, b: vw}}}
}
test('products of products stay sound', () => {
  let proven = 0, falseSeen = 0, randomAccepted = 0, deep = 0
  for (let t = 0; t < 300 * scale; t++) {
    const co = [rand(3), rand(3), 1 + rand(2)], w: E = rand(2) ? {op: 'var', name: 'z'} : {op: 'var', name: 'x'}
    const X: E = {op: 'var', name: 'x'}, Y: E = {op: 'var', name: 'y'}
    const slack = rand(3) // x <= y + slack: true only at slack 0
    const flip = rand(4) === 0 // claim p(y) <= p(x) instead: false
    const hyp: C = {op: '<=', a: X, b: slack ? {op: 'add', a: Y, b: {op: 'const', value: slack}} : Y}
    const claim: C = flip ? {op: '<=', a: mono(Y, w, co), b: mono(X, w, co)} : {op: '<=', a: mono(X, w, co), b: mono(Y, w, co)}
    const goal: Goal = {name: 'monotone', hyps: [hyp, {op: 'not', x: claim}]}
    const sat = [...models()].some(env => goal.hyps.every(h => evC(h, env)))
    if (sat) falseSeen++
    const out = timed('degree three', goal, () => grow(goal))
    if ('tree' in out && check(goal, out.tree)) { if (sat) throw new Error(`UNSOUND: ${JSON.stringify(goal)}`); proven++ }
    else if (!sat && slack === 0 && !flip) throw new Error(`a true monotonicity law not proven: ${JSON.stringify(co)}`)
    // A leaf at the root with random pairs, some naming product rows, and whatever derivation the solver finds.
    const rows = leafConstraints(goal, new Map())
    for (let tries = 0; tries < 20; tries++) {
      const pairs: [number, number][] = []
      for (let i = 0; i < 10; i++) pairs.push([rand(rows.length + pairs.length), rand(rows.length + pairs.length)])
      const verdict = solve(withProducts(rows, pairs))
      if (verdict.kind !== 'refuted' || !check(goal, {leaf: verdict.steps, products: pairs})) continue
      randomAccepted++
      if (sat) throw new Error(`UNSOUND (random products): ${JSON.stringify(goal)} ${JSON.stringify(pairs)}`)
      const shallow = pairs.map(([i, j]) => (i >= rows.length || j >= rows.length ? [0, 0] as [number, number] : [i, j] as [number, number]))
      if (solve(withProducts(rows, shallow)).kind !== 'refuted') deep++
    }
  }
  console.log(`degree three: ${proven} monotonicity laws proven, ${falseSeen} false variants (none accepted), ${randomAccepted} random-product leaves accepted (${deep} needing a product of a product), all with no model`)
  expect(proven).toBeGreaterThan(30) // every true one is proven (checked above); how many are true varies by seed
  expect(falseSeen).toBeGreaterThan(50)
  expect(randomAccepted).toBeGreaterThan(0) // products of products: a few per shard, summed over modal/suite.json's 32 shards
}, 600000)
