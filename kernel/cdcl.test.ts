// kernel/cdcl.ts's search by brute force: random linear goals (ifs, mins, maxes, truncation, map reads, conjunctions and
// disjunctions), larger than kernel.test.ts's so that cases multiply. Every tree the search returns is checked by the
// kernel, and no concrete model (x, y, z, w in 0..3, the map M any function from 0..3 to 0..3, 0 elsewhere) may satisfy
// a goal it refutes; a goal it calls satisfiable must not be one the plain search (prove.ts's grow) refutes, nor the
// other way round. FUZZ_SEED and FUZZ_SCALE shard it, as kernel.test.ts; GDP_CDCL_VERIFY=1 (the suite's shards) also
// compares reader.ts's rows with kernel.ts's at every node of the search and every leaf of the unfolded tree.
import {expect, test} from 'bun:test'
import {type C, type E, seeded} from '../core/machine.ts'
import type {Lin} from '../core/solver.ts'
import {type Goal, type Path, canon, check, leafConstraints, termColumn} from './kernel.ts'
import {clock, grow} from './prove.ts'
import {REFUTED, growCdcl} from './cdcl.ts'
import {Reader} from './reader.ts'

const scale = Number(process.env.FUZZ_SCALE ?? 1)
// (core/machine.ts's generator: exact since its float form folded every seed into a few short cycles, a seed on a short
// one drawing a handful of goals, all one way)
const rand = seeded(Number(process.env.FUZZ_SEED ?? 4242))
// A test's draws: n, then more while an outcome it counts is short (a seed whose goals all fell one way tests nothing
// about the other), up to `most`. A count still short fails as COVERAGE: the harness's failure, not the kernel's (the
// treadmill files it apart from a soundness failure).
const draws = function* (n: number, most: number, short: () => boolean) { for (let t = 0; t < most && (t < n || short()); t++) yield t }
const covered = (what: string, count: number, least = 1) => expect(count, `COVERAGE: ${what}: ${count}, under ${least}`).toBeGreaterThanOrEqual(least)
const names = ['x', 'y', 'z', 'w'] as const
const term = (d: number): E => {
  const r = rand(d <= 0 ? 2 : 9)
  if (r === 0) return {op: 'var', name: names[rand(4)]!}
  if (r === 1) return {op: 'const', value: rand(4)}
  if (r === 2) return {op: 'add', a: term(d - 1), b: term(d - 1)}
  if (r === 3) return {op: 'sub', a: term(d - 1), b: term(d - 1)}
  if (r === 4) return {op: 'min', a: term(d - 1), b: term(d - 1)}
  if (r === 5) return {op: 'max', a: term(d - 1), b: term(d - 1)}
  if (r === 6) return {op: 'if', c: cmp(d - 1), then: term(d - 1), else: term(d - 1)}
  if (r === 7) return {op: 'get', map: 'M', key: term(d - 1)}
  return {op: 'mul', k: 2, a: term(d - 1)}
}
const cmp = (d: number): C => {
  const r = rand(6)
  if (r === 3) return {op: 'not', x: cmp(d)}
  if (r >= 4 && d > 0) return {op: rand(2) ? 'and' : 'or', xs: [cmp(d - 1), cmp(d - 1), ...(rand(2) ? [cmp(d - 1)] : [])]}
  return {op: (['<', '<=', '='] as const)[rand(3)]!, a: term(d), b: term(d)}
}
type Env = {x: number, y: number, z: number, w: number, M: number[]}
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
  : c.op === 'flag' || c.op === 'all' ? false : c.op === '<' ? ev(c.a, env) < ev(c.b, env) : c.op === '<=' ? ev(c.a, env) <= ev(c.b, env) : ev(c.a, env) === ev(c.b, env)
const models = function* (): Generator<Env> {
  for (let m = 0; m < 256; m++) {
    const M = [m & 3, (m >> 2) & 3, (m >> 4) & 3, (m >> 6) & 3]
    for (let x = 0; x < 4; x++) for (let y = 0; y < 4; y++) for (let z = 0; z < 4; z++) for (let w = 0; w < 4; w++) yield {x, y, z, w, M}
  }
}

test('every tree the CDCL search returns checks, and refutes only goals with no model', () => {
  let proven = 0, sat = 0, unknown = 0
  for (const _ of draws(150 * scale, 600 * scale, () => !proven || !sat)) {
    const goal: Goal = {name: 'random', hyps: Array.from({length: 4 + rand(4)}, () => cmp(rand(3)))}
    const out = growCdcl(goal, new Map(), {nodes: 0, until: clock() + 5_000})
    const plain = grow(goal, new Map(), {nodes: 0, until: clock() + 5_000, units: false})
    if ('tree' in out) {
      proven++
      expect(check(goal, out.tree)).toBe(true)
      for (const env of models()) if (goal.hyps.every(h => evC(h, env))) throw new Error(`a model of a refuted goal: ${JSON.stringify(env)} ${JSON.stringify(goal)}`)
      expect('stuck' in plain && plain.stuck === 'sat').toBe(false)
    } else if (out.stuck === 'sat') {
      sat++
      expect('tree' in plain).toBe(false)
    } else unknown++
  }
  console.log(`cdcl fuzz: ${proven} refuted, ${sat} satisfiable, ${unknown} unknown`)
  covered('cdcl refuted', proven)
  covered('cdcl satisfiable', sat)
}, 600_000)

// The clausal mode (a model alone): a goal it refutes has no model, the model it gives meets every hypothesis, and it
// agrees with the kernel's reading wherever both answer. (A goal reading the map M is the kernel's reading's alone.)
test('the clausal mode refutes only goals with no model, and its models meet the goal', () => {
  let refuted = 0, sat = 0, same = 0
  const reads = (x: unknown): boolean => JSON.stringify(x).includes('"op":"get"')
  for (const _ of draws(300 * scale, 1200 * scale, () => !refuted || !sat)) {
    const goal: Goal = {name: 'random', hyps: Array.from({length: 4 + rand(4)}, () => cmp(rand(3)))}
    if (reads(goal)) continue
    const out = growCdcl(goal, new Map(), {nodes: 0, until: clock() + 5_000}, {model: true, clausal: true})
    const kernel = growCdcl(goal, new Map(), {nodes: 0, until: clock() + 5_000}, {model: true})
    if (!('tree' in out) && out.why === REFUTED) {
      refuted++
      for (const env of models()) if (goal.hyps.every(h => evC(h, env))) throw new Error(`a model of a goal the clausal mode refutes: ${JSON.stringify(env)} ${JSON.stringify(goal)}`)
      if (!('tree' in kernel) && kernel.why === REFUTED) same++
    } else if (!('tree' in out) && out.stuck === 'sat' && out.witness) {
      sat++
      const w = out.witness, env = {x: w.x ?? 0, y: w.y ?? 0, z: w.z ?? 0, w: w.w ?? 0, M: []}
      for (const h of goal.hyps) if (!evC(h, env)) throw new Error(`the clausal mode's model breaks ${JSON.stringify(h)}: ${JSON.stringify(w)}`)
      if (!('tree' in kernel) && kernel.stuck === 'sat') same++
    }
  }
  console.log(`clausal fuzz: ${refuted} refuted, ${sat} satisfiable, ${same} as the kernel's reading`)
  covered('clausal refuted', refuted)
  covered('clausal satisfiable', sat)
}, 600_000)

// FUZZ_SEED=28018 (shrunk): a disjunction with one open part kept its facts as final although a part it took as false
// was false only through an open term column (1 ∸ y, read as its column while y ≤ 1 was open). Once y ≤ 1 was decided
// the column read 1 − y, that part opened, and kernel.ts gave the hypothesis no fact, but reader.ts kept 0 = 0's.
test("reader.ts keeps a disjunction's facts only while its closed parts' values are kept too", () => {
  const x: E = {op: 'var', name: 'x'}, y: E = {op: 'var', name: 'y'}, z: E = {op: 'var', name: 'z'}, n = (value: number): E => ({op: 'const', value})
  const cut = (): E => ({op: 'sub', a: n(1), b: y})
  const goal: Goal = {name: 'seed 28018', hyps: [
    {op: 'or', xs: [{op: '=', a: n(0), b: {op: 'if', c: {op: '<=', a: x, b: y}, then: x, else: n(0)}}, {op: 'not', x: {op: '<', a: cut(), b: x}}]},
    {op: '<', a: cut(), b: x},
    {op: '=', a: x, b: z},
  ]}
  // The search's trail: 1 ∸ y < x (its column), y < x, y ≤ 1, each decided true at a node of its own.
  const steps = ([{'1': 1, x: -1, [termColumn(cut())]: 1}, {'1': 1, x: -1, y: 1}, {'1': -1, y: 1}] as Lin[]).map(lin => ({name: canon(lin), lin, holds: true}))
  const trail: typeof steps = [], stamps: number[] = []
  const reader = new Reader(goal, {
    get: name => { const at = trail.findIndex(a => a.name === name); return at < 0 ? undefined : {val: trail[at]!.holds, at} },
    stamp: at => stamps[at]!, size: () => trail.length, lin: at => trail[at]!,
  })
  const texts = (lins: {lin: Lin}[]) => [...new Set(lins.map(r => canon(r.lin)))].sort()
  for (let i = 0; ; i++) {
    reader.begin()
    reader.sync()
    const path: Path = new Map(trail.map(a => [a.name, {lin: a.lin, holds: a.holds}]))
    expect(texts(reader.rows())).toEqual(texts(leafConstraints(goal, path)))
    expect(texts(reader.live)).toEqual(texts(leafConstraints(goal, path)))
    if (i === steps.length) break
    stamps[trail.length] = i + 1; trail.push(steps[i]!); reader.touch(steps[i]!.name)
  }
})
