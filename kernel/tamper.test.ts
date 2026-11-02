// Tampered proofs, against real trees (the models' and the examples' laws). Two kinds:
//   - structural: a leaf's derivation broken in a way the checker's rules forbid outright (an input out of range, a row
//     combined before it exists, a multiplier that is zero, negative or fractional, a cut whose divisor doesn't divide
//     or is zero, a derivation that ends on a row with a variable left, a split on a constant, a split repeated): each
//     must be rejected, whatever the goal;
//   - semantic: the goal weakened (a hypothesis dropped, a constant moved by one, a comparison loosened) until random
//     sampling finds a model of it: then the original tree, offered for the weakened goal, must be rejected, and so must
//     anything the prover grows for it.
//   - names every object has (constructor, __proto__, toString, valueOf, hasOwnProperty) as a rule's names: the same goals
//     and proofs as the plain names', and nothing false accepted, at random.
// This is what the mutation run (mutants.ts) leans on to see whether a change to kernel.ts or check.ts goes unnoticed.
import {expect, test} from 'bun:test'
import {type C, type E, type Law, type Machine, type State, evalC, interpret, seeded} from '../core/machine.ts'
import {admitFlagged, boundedLoss, capLaws, inflight, inflightLoss, loss, windowCeiling, windowLimit} from '../core/models.ts'
import {type Constraint, type Lin, type Step, add, k, scale, sub, v} from '../core/solver.ts'
import {checkRefutation, checkWitness} from '../core/check.ts'
import {type Goal, type Instances, type Loop, type QMachine, type StepLaw, type Tree, canon, check, checkLaws, checkQMachine, checkQTree, checkRecur, checkStepLaws, columnTerm, factorsOf, leafConstraints, loopObligations, obligations,
  progressObligations, qObligations, stepLawObligations, substE, sumMachine, termColumn} from './kernel.ts'
import {growQ} from './qprove.ts'
import {grow, parseKey, proveLaws, proveStepLaws, withWall} from './prove.ts'

// A count a test expects fails as COVERAGE: the harness's, not the kernel's (the treadmill files it apart from a
// soundness failure).
const rand = seeded(Number(process.env.FUZZ_SEED ?? 99))
const covered = (what: string, count: number, least = 1) => expect(count, `COVERAGE: ${what}: ${count}, under ${least}`).toBeGreaterThanOrEqual(least)

const strong: Law = {name: 's + 50p <= b + 150', holds: {op: '<=', a: {op: 'add', a: {op: 'var', name: 's'}, b: {op: 'mul', k: 50, a: {op: 'var', name: 'p'}}}, b: {op: 'add', a: {op: 'var', name: 'b'}, b: {op: 'const', value: 150}}}}
const subjects: [Machine, Law[]][] = [[loss(), [boundedLoss]], [inflight, [inflightLoss, strong]], [admitFlagged(), capLaws], [windowLimit(), [windowCeiling]]]
const proofs: {goal: Goal, tree: Tree}[] = []
for (const [m, laws] of subjects) {
  const r = proveLaws(m, laws)
  if (!r.proven || !r.proof) throw new Error(`${m.name}: not proven`)
  for (const g of obligations(m, laws, r.proof.instances)) proofs.push({goal: g, tree: r.proof.trees[g.name]!})
}

// Nonlinear goals: products of cells, and refutations that need squares (Cauchy–Schwarz's (ad − bc)², AM–GM for three,
// a square of factors shifted by a step, a³ <= b³ only when a <= b).
{
  const X = (name: string): E => ({op: 'var', name}), P = (a: E, b: E): E => ({op: 'prod', a, b}), S = (a: E, b: E): E => ({op: 'add', a, b})
  const le = (a: E, b: E): C => ({op: '<=', a, b}), not = (c: C): C => ({op: 'not', x: c}), K = (value: number): E => ({op: 'const', value})
  const [a, b, c, d] = ['a', 'b', 'c', 'd'].map(X) as [E, E, E, E], cell = (map: string, k: string): E => ({op: 'get', map, key: X(k)})
  const nonlinear: Goal[] = [
    {name: 'cauchy-schwarz', hyps: [not(le(P(S(P(a, c), P(b, d)), S(P(a, c), P(b, d))), P(S(P(a, a), P(b, b)), S(P(c, c), P(d, d)))))]},
    {name: 'am-gm for three', hyps: [not(le(P(S(P(a, b), P(a, b)), c), S(S(P(P(a, a), a), P(P(b, b), b)), P(P(c, c), c))))]},
    {name: 'a shifted square', hyps: [le(K(1), b), le(P(S(a, b), S(a, b)), K(1000)), not(le({op: 'mul', k: 4, a: P(S(a, K(1)), {op: 'sub', a: b, b: K(1)})}, P(S(a, b), S(a, b))))]},
    {name: 'cubes', hyps: [le(P(P(a, a), a), P(P(b, b), b)), not(le(a, b))]},
    {name: 'a cell times a param', hyps: [le(cell('U', 'k'), P(X('per'), cell('S', 'k'))), not(le(S(cell('U', 'k'), X('per')), P(X('per'), S(cell('S', 'k'), K(1)))))]},
  ]
  for (const g of nonlinear) {
    const out = grow(g)
    if (!('tree' in out)) throw new Error(`${g.name}: not proven`)
    proofs.push({goal: g, tree: out.tree})
  }
}
const squaresIn = (t: Tree): number => ('leaf' in t ? t.squares?.length ?? 0 : squaresIn(t.yes) + squaresIn(t.no))
test('nonlinear proofs: squares are read, and a changed square breaks them', () => {
  let squared = 0, changed = 0
  for (const {goal, tree} of proofs.filter(p => squaresIn(p.tree) > 0)) {
    squared++
    expect(check(goal, tree)).toBe(true)
    const drop = (t: Tree): Tree => ('leaf' in t ? {leaf: t.leaf, ...(t.products ? {products: t.products} : {})} : {...t, yes: drop(t.yes), no: drop(t.no)})
    expect(check(goal, drop(tree)), `${goal.name} without its squares`).toBe(false)
    // Each square's form moved by one somewhere: if the kernel still accepts, the goal must still have no model.
    for (let k = 0; k < 20; k++) {
      const copy = structuredClone(tree), leaf = leaves(copy).find(l => l.squares?.length)! as Leaf & {squares: Record<string, number>[]}
      const sq = leaf.squares[rand(leaf.squares.length)]!, keys = Object.keys(sq), key = keys[rand(keys.length)]!
      sq[key] = sq[key]! + (rand(2) ? 1 : -1)
      if (!check(goal, copy)) changed++
      else expect(model(goal), `${goal.name}: a changed square accepted, and the goal has a model`).toBe(false)
    }
  }
  console.log(`tamper: ${squared} proofs with squares, ${changed} changed squares rejected`)
  covered('proofs with squares', squared, 3)
  covered('changed squares rejected', changed)
})

type Leaf = Extract<Tree, {leaf: Step[]}>
const leaves = (t: Tree): Leaf[] => ('leaf' in t ? [t] : [...leaves(t.yes), ...leaves(t.no)])
const splits = (t: Tree): (Tree & {split: object})[] => ('leaf' in t ? [] : [t, ...splits(t.yes), ...splits(t.no)])

test('structurally broken derivations are rejected', () => {
  let tried = 0
  for (const {goal, tree} of proofs) {
    expect(check(goal, tree)).toBe(true)
    for (let k = 0; k < leaves(tree).length; k++) {
      const tampers: ((leaf: Step[]) => boolean)[] = [
        leaf => { const i = leaf.findIndex(s => s.kind === 'input'); if (i < 0) return false; leaf[i] = {kind: 'input', index: 10_000}; return true },
        leaf => { const i = leaf.findIndex(s => s.kind === 'combine'); if (i < 0) return false; const s = leaf[i] as Step & {kind: 'combine'}; leaf[i] = {...s, a: i}; return true },
        leaf => { const i = leaf.findIndex(s => s.kind === 'combine'); if (i < 0) return false; leaf[i] = {...(leaf[i] as Step & {kind: 'combine'}), ma: 0}; return true },
        leaf => { const i = leaf.findIndex(s => s.kind === 'combine'); if (i < 0) return false; leaf[i] = {...(leaf[i] as Step & {kind: 'combine'}), mb: -1}; return true },
        leaf => { const i = leaf.findIndex(s => s.kind === 'combine'); if (i < 0) return false; leaf[i] = {...(leaf[i] as Step & {kind: 'combine'}), ma: 1.5}; return true },
        leaf => { const i = leaf.findIndex(s => s.kind === 'cut'); if (i < 0) return false; leaf[i] = {...(leaf[i] as Step & {kind: 'cut'}), g: 0}; return true },
        leaf => { const i = leaf.findIndex(s => s.kind === 'cut'); if (i < 0) return false; const s = leaf[i] as Step & {kind: 'cut'}; leaf[i] = {...s, of: i}; return true },
        leaf => { leaf.length = 0; return true },
        leaf => { const i = leaf.findIndex(s => s.kind === 'combine'); if (i < 0) return false; const s = leaf[i] as Step & {kind: 'combine'}; leaf[i] = {...s, b: i}; return true },
        leaf => { const i = leaf.findIndex(s => s.kind === 'combine'); if (i < 0) return false; const s = leaf[i] as Step & {kind: 'combine'}; leaf[i] = {...s, a: 10_000}; return true },
      ]
      for (const tamper of tampers) {
        const copy = structuredClone(tree), leaf = leaves(copy)[k]!.leaf
        if (!tamper(leaf)) continue
        tried++
        expect(check(goal, copy), `${goal.name}: ${tamper.toString().slice(0, 60)}`).toBe(false)
      }
    }
    // A split on a constant, and a split repeated under itself.
    for (let k = 0; k < splits(tree).length; k++) {
      const copy = structuredClone(tree), sp = splits(copy)[k]!
      ;(sp as {split: Record<string, number>}).split = {'1': 1}
      expect(check(goal, copy)).toBe(false)
      const again = structuredClone(tree), s2 = splits(again)[k]! as Tree & {split: Record<string, number>, yes: Tree, no: Tree}
      s2.yes = {split: s2.split, yes: s2.yes, no: s2.yes}
      expect(check(goal, again)).toBe(false)
      tried += 2
    }
  }
  console.log(`tamper: ${proofs.length} real goals, ${tried} structurally broken trees, all rejected`)
  covered('structurally broken trees', tried, 101)
})

// Weakened goals: random sampling (variables and map cells over a small range) for a model; when one is found, the
// original tree and anything the prover grows for the weakened goal must be rejected.
const vars = (t: unknown): string[] => [...new Set([...JSON.stringify(t).matchAll(/"op":"var","name":"([^"]+)"/g)].map(m => m[1]!))]
const evE = (e: E, env: Record<string, number>, cells: (map: string, key: number) => number): number => {
  switch (e.op) {
    case 'var': return env[e.name] ?? 0
    case 'const': return e.value
    case 'add': return evE(e.a, env, cells) + evE(e.b, env, cells)
    case 'sub': return Math.max(0, evE(e.a, env, cells) - evE(e.b, env, cells))
    case 'mul': return e.k * evE(e.a, env, cells)
    case 'prod': return evE(e.a, env, cells) * evE(e.b, env, cells)
    case 'min': return Math.min(evE(e.a, env, cells), evE(e.b, env, cells))
    case 'max': return Math.max(evE(e.a, env, cells), evE(e.b, env, cells))
    case 'if': return evC(e.c, env, cells) ? evE(e.then, env, cells) : evE(e.else, env, cells)
    case 'get': return cells(e.map, evE(e.key, env, cells))
  }
}
const evC = (c: C, env: Record<string, number>, cells: (map: string, key: number) => number): boolean => {
  switch (c.op) {
    case 'all': throw new Error('no quantified flags here')
    case '<': return evE(c.a, env, cells) < evE(c.b, env, cells)
    case '<=': return evE(c.a, env, cells) <= evE(c.b, env, cells)
    case '=': return evE(c.a, env, cells) === evE(c.b, env, cells)
    case 'and': return c.xs.every(x => evC(x, env, cells))
    case 'or': return c.xs.some(x => evC(x, env, cells))
    case 'not': return !evC(c.x, env, cells)
    case 'flag': throw new Error('flags are inlined in goals')
  }
}
function model(goal: Goal, tries = 20_000): boolean {
  const names = vars(goal.hyps)
  for (let i = 0; i < tries; i++) {
    const range = 1 + rand(i < tries / 2 ? 4 : 40)
    const env = Object.fromEntries(names.map(n => [n, rand(range)]))
    const table = new Map<string, number>()
    const cells = (map: string, key: number) => { const id = `${map}[${key}]`; if (!table.has(id)) table.set(id, rand(range)); return table.get(id)! }
    if (goal.hyps.every(h => evC(h, env, cells))) return true
  }
  return false
}
const loosen = (c: C): C[] => {
  switch (c.op) {
    case 'all': throw new Error('no quantified flags here')
    case '<': return [{...c, op: '<='}, {op: '<', a: c.a, b: {op: 'add', a: c.b, b: {op: 'const', value: 1}}}]
    case '<=': return [{op: '<=', a: c.a, b: {op: 'add', a: c.b, b: {op: 'const', value: 1}}}]
    case '=': return [{op: '<=', a: c.a, b: c.b}]
    case 'and': case 'or': case 'not': case 'flag': return []
  }
}

test('a proof offered for a weakened goal with a model is rejected', () => {
  let weakened = 0, withModel = 0
  for (const {goal, tree} of proofs) {
    const variants: Goal[] = []
    for (let i = 0; i < goal.hyps.length; i++) {
      variants.push({name: `${goal.name} without hypothesis ${i}`, hyps: goal.hyps.filter((_, j) => j !== i)})
      for (const l of loosen(goal.hyps[i]!)) variants.push({name: `${goal.name} with hypothesis ${i} loosened`, hyps: goal.hyps.map((h, j) => (j === i ? l : h))})
    }
    for (const v of variants) {
      weakened++
      if (!model(v)) continue
      withModel++
      expect(check(v, tree), v.name).toBe(false)
      const out = grow(v, new Map(), {nodes: 0, until: performance.now() + 2000})
      if ('tree' in out) expect(check(v, out.tree), `grown for ${v.name}`).toBe(false)
    }
  }
  console.log(`tamper: ${weakened} weakened goals, ${withModel} with a model found, every proof offered for them rejected`)
  covered('weakened goals with a model found', withModel, 31)
}, 600_000)

test('derivations that only an unsound checker would accept, and witnesses', () => {
  // 2x + y - 1 <= 0 and 1 - y <= 0 hold at x = 0, y = 1. A cut of the first by 2 needs every coefficient divisible (y's
  // isn't): rounding the constant up is sound only for integer rows. Accepting it would derive 1 <= 0.
  const constraints: Constraint[] = [{lin: {x: 2, y: 1, '1': -1}, label: 'a'}, {lin: {y: -1, '1': 1}, label: 'b'}, {lin: {x: -1}, label: 'x >= 0'}]
  const steps: Step[] = [{kind: 'input', index: 0}, {kind: 'cut', of: 0, g: 2}, {kind: 'input', index: 1}, {kind: 'combine', a: 1, b: 2, ma: 2, mb: 1}, {kind: 'input', index: 2}, {kind: 'combine', a: 3, b: 4, ma: 1, mb: 2}]
  expect(checkRefutation(constraints, steps)).toBe(false)
  expect(checkWitness(constraints, {x: 0, y: 1})).toBe(true)
  // A valid refutation of an unsatisfiable system, and its broken forms.
  const unsat: Constraint[] = [{lin: {x: 1, '1': 1}, label: 'x <= -1'}, {lin: {x: -1}, label: 'x >= 0'}]
  const ok: Step[] = [{kind: 'input', index: 0}, {kind: 'input', index: 1}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]
  expect(checkRefutation(unsat, ok)).toBe(true)
  expect(checkRefutation(unsat, [...ok.slice(0, 2), {kind: 'combine', a: 0, b: 2, ma: 1, mb: 1}])).toBe(false) // b names itself
  expect(checkRefutation(unsat, [...ok.slice(0, 2), {kind: 'combine', a: 0, b: 1, ma: 0, mb: 1}])).toBe(false)
  expect(checkRefutation(unsat, [...ok.slice(0, 2), {kind: 'combine', a: 0, b: 1, ma: 1, mb: 0}])).toBe(false)
  expect(checkRefutation(unsat, [{kind: 'input', index: 2}])).toBe(false)
  expect(checkRefutation(unsat, [...ok, {kind: 'cut', of: 2, g: 0}])).toBe(false)
  expect(checkRefutation(unsat, [...ok, {kind: 'cut', of: 3, g: 1}])).toBe(false) // a cut of a row not made yet
  // Witnesses: at most 0 is satisfied, above is not, a missing variable is not.
  expect(checkWitness([{lin: {x: 1, '1': -3}, label: ''}], {x: 3})).toBe(true)
  expect(checkWitness([{lin: {x: 1, '1': -3}, label: ''}], {x: 4})).toBe(false)
  expect(checkWitness([{lin: {x: 1, y: 1}, label: ''}], {x: 0})).toBe(false)
  expect(checkWitness([{lin: {x: 1, '1': -3}, label: ''}, {lin: {x: -1, '1': 5}, label: ''}], {x: 3})).toBe(false) // the second fails
  // Product pairs that name no row are ignored, not trusted or crashed on.
  const {goal, tree} = proofs.find(p => 'leaf' in p.tree) ?? proofs[0]!
  const withBad = (t: Tree): Tree => ('leaf' in t ? {...t, products: [...(t.products ?? []), [10_000, 0], [0, 10_000]]} : {...t, yes: withBad(t.yes), no: withBad(t.no)})
  expect(check(goal, withBad(tree))).toBe(check(goal, tree))
})

// --- names every object has --------------------------------------------------------------------------------------------
// A rule's or a certificate's name may be constructor, toString, valueOf, hasOwnProperty or __proto__: what every object
// reads through its prototype, or sets when assigned (__proto__). The kernel reads each as a name like any other: a
// substitution, a run's frame, a law's instances, a step law's own instances and a loop's values by their own entries
// alone, and every linear form built on no prototype. (Through the prototype a map constructor read before a step was
// Object(key), the key itself, and a variable __proto__ fell out of every row, so 1 <= __proto__ read 1 <= 0: false laws
// accepted, Lean never fooled; terra's review of gen/laneC3, then gen/laneH3's audit.)
const PROTO = ['constructor', '__proto__', 'toString', 'valueOf', 'hasOwnProperty']
type Rn = (name: string) => string
// Each name renamed at its base, the kernel's own names around it kept (?f, w?f, x', x~1, a@2, k#).
const renamer = (ren: Map<string, string>): Rn => n => n.replace(/^((?:w\d*)?\?)?([A-Za-z_][A-Za-z0-9_]*)/, (all, pre: string | undefined, base: string) => (ren.has(base) ? `${pre ?? ''}${ren.get(base)}` : all))
const renameT = <T>(t: T, rn: Rn): T => {
  if (Array.isArray(t)) return t.map(x => renameT(x, rn)) as T
  if (!t || typeof t !== 'object') return t
  const o = t as Record<string, unknown>, named = (key: string) => (key === 'name' && (o.op === 'var' || o.op === 'flag')) || (key === 'map' && o.op === 'get') || (key === 'key' && o.op === 'all')
  return Object.fromEntries(Object.entries(o).map(([key, x]) => [key, named(key) ? rn(x as string) : key === 'keys' && o.op === 'all' ? (x as string[]).map(rn) : renameT(x, rn)])) as T
}
// A row's names: variables, cells (their keys' canonical text read again), monomials and term columns.
const renameKey = (key: string, rn: Rn): string => {
  const col = columnTerm(key), fs = factorsOf(key), at = key.indexOf('[')
  return key === '1' ? key : col ? termColumn(renameT(col, rn)) : fs.length > 1 ? fs.map(f => renameKey(f, rn)).sort().join('*')
    : at < 0 ? rn(key) : `${rn(key.slice(0, at))}[${canon(renameLin(parseKey(key.slice(at + 1, -1)), rn))}]`
}
const renameLin = (lin: Lin, rn: Rn): Lin => Object.fromEntries(Object.entries(lin).map(([key, c]) => [renameKey(key, rn), c]))
const renameTree = (t: Tree, rn: Rn): Tree => ('leaf' in t ? {...t, ...(t.squares ? {squares: t.squares.map(q => renameLin(q, rn))} : {})} : {split: renameLin(t.split, rn), yes: renameTree(t.yes, rn), no: renameTree(t.no, rn)})
const renamed = <T>(r: Record<string, T> | undefined, rn: Rn, f: (x: T) => T): Record<string, T> | undefined => r && Object.fromEntries(Object.entries(r).map(([n, x]) => [rn(n), f(x)]))
const renameLaw = (l: Law, rn: Rn): Law => ({...l, name: rn(l.name), holds: renameT(l.holds, rn), ...(l.forall ? {forall: rn(l.forall)} : {}), ...(l.keys ? {keys: l.keys.map(rn)} : {})})
const renameMachine = (m: Machine, rn: Rn): Machine => {
  const t = <T>(x: T) => renameT(x, rn)
  return {...m, params: m.params.map(rn), inputs: m.inputs.map(rn), state: renamed(m.state, rn, t)!, maps: renamed(m.maps, rn, x => x), inputMaps: m.inputMaps?.map(rn),
    fns: renamed(m.fns, rn, x => x), facts: m.facts?.map(l => renameLaw(l, rn)), pre: m.pre && t(m.pre), assume: m.assume && t(m.assume),
    step: {flags: renamed(m.step.flags, rn, t), state: renamed(m.step.state, rn, t), maps: renamed(m.step.maps, rn, w => ('each' in w ? {each: rn(w.each), value: t(w.value)} : t(w)))}}
}
const renameInstances = (i: Instances, rn: Rn): Instances => renamed(i, rn, es => es.map(e => renameT(e, rn)))!
const renameTrees = (ts: Record<string, Tree>, rn: Rn): Record<string, Tree> => renamed(ts, rn, t => renameTree(t, rn))!
const renameGoals = (gs: Goal[], rn: Rn): Goal[] => gs.map(g => ({name: rn(g.name), hyps: renameT(g.hyps, rn)}))
// A machine's names, each renamed to one of PROTO (as many as there are, in a drawn order).
const protoNames = (names: string[], draw: (n: number) => number): Rn => {
  const pool = [...PROTO], ren = new Map<string, string>()
  for (const n of names) if (pool.length && draw(2)) ren.set(n, pool.splice(draw(pool.length), 1)[0]!)
  return renamer(ren)
}
const namesOf = (m: Machine): string[] => [...m.params, ...m.inputs, ...Object.keys(m.state), ...Object.keys(m.maps ?? {}), ...Object.keys(m.step.flags ?? {}), ...(m.inputMaps ?? []), ...Object.keys(m.fns ?? {})]

test('a name every object has is a name like any other: rows, goals and substitutions', () => {
  for (const P of PROTO) {
    // Rows keep it, and check.ts sums it: 1 - P <= 0 (P >= 1, true at P = 1) is refuted by no combination of itself.
    expect(sub(k(1), v(P))).toEqual(JSON.parse(`{"1": 1, "${P}": -1}`))
    expect(add(v(P), v(P), k(1))).toEqual(JSON.parse(`{"${P}": 2, "1": 1}`))
    expect(scale(v(P), 3)).toEqual(JSON.parse(`{"${P}": 3}`))
    const row: Lin = JSON.parse(`{"${P}": -1, "1": 1}`)
    expect(checkRefutation([{lin: row, label: ''}], [{kind: 'input', index: 0}, {kind: 'combine', a: 0, b: 0, ma: 1, mb: 1}]), P).toBe(false)
    expect(checkWitness([{lin: JSON.parse(`{"${P}": 1, "1": -3}`), label: ''}], {}), P).toBe(false)
    // Goals: 1 <= P has a model; nothing refutes it, over the naturals or the rationals.
    const X: E = {op: 'var', name: P}, K = (value: number): E => ({op: 'const', value}), le = (a: E, b: E): C => ({op: '<=', a, b})
    expect(check({name: P, hyps: [le(K(1), X)]}, {leaf: [{kind: 'input', index: 0}]}), P).toBe(false)
    expect(check({name: P, hyps: [le(K(1), {op: 'prod', a: X, b: K(1)})]}, {leaf: [{kind: 'input', index: 0}]}), `${P} · 1`).toBe(false)
    expect(checkQTree({name: P, hyps: [{op: '<=', a: {op: 'const', q: {num: 1n, den: 1n}}, b: {op: 'var', name: P}}]}, {leaf: [{kind: 'input', index: 0}]}), P).toBe(false)
    // P <= 2 and 3 <= P have none: proven and checked. A cell at P and one at 0 are two cells while P >= 1.
    const none: Goal = {name: P, hyps: [le(X, K(2)), le(K(3), X)]}, proven = grow(none)
    expect('tree' in proven && check(none, proven.tree), P).toBe(true)
    for (const map of ['M', P]) {
      const cells: Goal = {name: P, hyps: [le(K(1), {op: 'get', map, key: X}), le({op: 'get', map, key: K(0)}, K(0)), le(K(1), X)]}, out = grow(cells, new Map(), {nodes: 0, until: performance.now() + 2000})
      if ('tree' in out) expect(check(cells, out.tree), `${P}: ${map}[${P}] and ${map}[0]`).toBe(false)
    }
    // A substitution reads its own entries.
    const e: E = {op: 'get', map: P, key: X}
    expect(substE(e, {vars: {}, maps: {}, flags: {}})).toEqual(e)
  }
})

test('a rule whose names every object has: the same goals, the same proofs, nothing false', () => {
  const K = (value: number): E => ({op: 'const', value}), X = (name: string): E => ({op: 'var', name})
  for (const P of PROTO) {
    const rn = renamer(new Map([['M', P]]))
    // A map written at 0 alone, s counting the steps: s <= M[s + 1] is false after one step (s = 1, every cell 0); read
    // through the prototype, the map before the step was the key itself, and the law proven.
    const counter = (map: string): Machine => ({name: 'counter', params: [], inputs: [], state: {s: K(0)}, maps: {[map]: 0}, step: {state: {s: {op: 'add', a: X('s'), b: K(1)}}, maps: {[map]: {key: K(0), value: K(0)}}}})
    const laws = (map: string): Law[] => [{name: 'L', holds: {op: '<=', a: X('s'), b: {op: 'get', map, key: {op: 'add', a: X('s'), b: K(1)}}}}]
    expect(obligations(counter(P), laws(P))).toEqual(renameGoals(obligations(counter('M'), laws('M')), rn))
    expect(withWall(performance.now() + 3000, () => proveLaws(counter(P), laws(P))).proven, P).toBe(false)
    // A map no step writes: M'[k] = k is false (M' = M, every cell 0); read through the prototype, M' was the key.
    const still = (map: string): Machine => ({name: 'still', params: [], inputs: [], state: {s: K(0)}, maps: {[map]: 0}, step: {state: {s: X('s')}}})
    const frame = (map: string): StepLaw => ({name: 'frame', forall: 'k', then: {op: '=', a: {op: 'get', map: `${map}'`, key: X('k')}, b: X('k')}})
    expect(stepLawObligations(still(P), [], {}, frame(P))).toEqual(renameGoals(stepLawObligations(still('M'), [], {}, frame('M')), rn))
    expect(withWall(performance.now() + 3000, () => proveStepLaws(still(P), [], [frame(P)])).proven, P).toBe(false)
  }
  // The models' proofs, each name of each machine (a param, an input, a state variable, a map, a flag) and each law's
  // name renamed to each of PROTO, and every name at once: the goals renamed, the proofs still check.
  let checked = 0
  for (const [m, laws] of subjects.filter(([m]) => !m.history)) {
    const r = proveLaws(m, laws)
    if (!r.proven || !r.proof) throw new Error(`${m.name}: not proven`)
    const lawName = (n: string, P: string): Rn => x => (x === n ? P : x.startsWith(`${n} @`) ? P + x.slice(n.length) : x)
    const rns = [...namesOf(m).flatMap(n => PROTO.map(P => renamer(new Map([[n, P]])))), ...laws.flatMap(l => PROTO.map(P => lawName(l.name, P))), renamer(new Map(namesOf(m).slice(-5).map((n, i) => [n, PROTO[i]!])))]
    for (const rn of rns) {
      const rm = renameMachine(m, rn), rl = laws.map(l => renameLaw(l, rn)), inst = renamed(r.proof.instances, rn, i => renameInstances(i, rn))!
      expect(obligations(rm, rl, inst)).toEqual(renameGoals(obligations(m, laws, r.proof.instances), rn))
      expect(checkLaws(rm, rl, {instances: inst, trees: renameTrees(r.proof.trees, rn)}), m.name).toBe(true)
      checked++
    }
  }
  covered('renamed proofs checked', checked, 100)
}, 600_000)

// Each check that asks whether a rule declares a name asks its own entries: a sum, its key and its map, a loop's body, a
// progress claim's request and a rational machine's step, each named as every object's names.
test('a sum, a loop, a request and a rational step whose names every object has', () => {
  const X = (name: string): E => ({op: 'var', name}), K = (value: number): E => ({op: 'const', value}), get = (map: string, key: E): E => ({op: 'get', map, key})
  const bank = (map: string, s: string, key: string, read = map): Machine => ({name: 'bank', params: ['supply'], inputs: ['to', 'amt'], state: {}, maps: {[map]: 0},
    step: {maps: {[map]: {key: X('to'), value: {op: 'add', a: get(map, X('to')), b: X('amt')}}}}, sums: {[s]: {key, term: get(read, X(key))}}})
  const q0 = {num: 0n, den: 1n}
  for (const P of PROTO) {
    for (const [map, s, key] of [['Bal', P, 'k$S'], ['Bal', 'S', P], [P, 'S', 'k$S']]) expect(() => sumMachine(bank(map!, s!, key!)), `${map} ${s} ${key}`).not.toThrow()
    expect(() => sumMachine(bank('Bal', 'S', 'k$S', P))).toThrow(/not a map/)
    // (a sum named so keeps its step: the goals are the plain sum's, renamed; terra's review of gen/laneH3, a sum __proto__ lost it)
    const sumRn: Rn = n => n.replace(/(^|[$?])S(?=$|['~@# ])/g, (_, at: string) => at + P), atMost = (s: string): Law[] => [{name: 'L', holds: {op: '<=', a: X(s), b: X('supply')}}]
    expect(obligations(bank('Bal', P, 'k$S'), atMost(P))).toEqual(renameGoals(obligations(bank('Bal', 'S', 'k$S'), atMost('S')), sumRn))
    expect(() => sumMachine({...bank('Bal', 'S', P), state: {[P]: K(0)}})).toThrow(/already a name of the machine/)
    const loop: Loop = {name: 'loop', params: [], inputs: [], state: {x: K(0)}, while: {op: '<', a: X('x'), b: K(3)}, body: {x: {op: 'add', a: X('x'), b: K(1)}, [P]: K(0)}}
    expect(() => loopObligations(loop, [], {op: 'sub', a: K(3), b: X('x')})).toThrow(/body sets/)
    expect(() => checkRecur(loop, {start: {}, stem: [], set: {op: '<=', a: K(0), b: X('x')}, wit: {}, tree: {leaf: []}})).toThrow(/body sets/)
    const asks: Machine = {name: 'asks', params: [], inputs: [P], state: {s: K(0)}, step: {state: {s: X(P)}}}
    expect(() => progressObligations(asks, [], {}, {name: 'some request', when: {op: '<=', a: K(0), b: K(0)}, then: {op: '<=', a: K(0), b: K(0)}, request: {}})).toThrow(/outside the kernel/)
    // A rational state variable no step sets keeps its value: P <= 0 holds throughout.
    const qm: QMachine = {name: 'q', params: [], inputs: [], state: {[P]: {op: 'const', q: q0}}, step: {}}, law = {name: 'stays', holds: {op: '<=', a: {op: 'var', name: P}, b: {op: 'const', q: q0}} as const}
    const goals = qObligations(qm, [law], law), tree = (g: typeof goals.start): Tree => { const o = growQ(g); if (!('tree' in o)) throw new Error(`${P}: ${o.stuck}`); return o.tree }
    expect(checkQMachine(qm, [law], {stays: {start: tree(goals.start), step: tree(goals.step)}}), P).toBe(true)
  }
})

// The fuzz: random goals and random machines with step laws, their names drawn among PROTO. A proof of the plain goal,
// renamed, checks exactly when the plain one does; and where the plain goal has a model (the plain machine a run that
// breaks the law), no tree of the shapes the prototype let through (a leaf reading one row, alone or doubled; another
// goal's proof, renamed) is accepted of the renamed one. (The prover itself is untrusted and may stall on such names:
// it is never asked about them here.)
const fz = (d: number): E => {
  const r = rand(d <= 0 ? 2 : 9)
  if (r === 0) return {op: 'var', name: ['x', 'y', 'z'][rand(3)]!}
  if (r === 1) return {op: 'const', value: rand(4)}
  if (r === 7) return {op: 'get', map: 'M', key: fz(d - 1)}
  if (r === 8) return {op: 'if', c: fc(d - 1), then: fz(d - 1), else: fz(d - 1)}
  return {op: (['add', 'sub', 'min', 'max', 'add'] as const)[r - 2]!, a: fz(d - 1), b: fz(d - 1)}
}
const fc = (d: number): C => (rand(5) === 4 ? {op: 'not', x: fc(d)} : {op: (['<', '<=', '='] as const)[rand(3)]!, a: fz(d), b: fz(d)})
const small = (g: Goal): boolean => {
  for (let m = 0; m < 256; m++) for (let x = 0; x < 4; x++) for (let y = 0; y < 4; y++) for (let z = 0; z < 4; z++) {
    const env = {x, y, z}, cells = (_: string, key: number) => (key < 4 ? (m >> (2 * key)) & 3 : 0)
    if (g.hyps.every(h => evC(h, env, cells))) return true
  }
  return false
}
test('names every object has, at random: renamed proofs check alike, and nothing false is accepted', () => {
  let same = 0, offered = 0, laws = 0, broken = 0
  const pool: Tree[] = [], shapes = (n: number): Tree[] => [...Array.from({length: n}, (_, i): Tree[] => [{leaf: [{kind: 'input', index: i}]},
    {leaf: [{kind: 'input', index: i}, {kind: 'combine', a: 0, b: 0, ma: 1, mb: 1}]}]).flat(), ...pool.slice(-4)]
  for (let t = 0; t < 60; t++) {
    const goal: Goal = {name: 'random', hyps: [fc(2), fc(2), fc(1)]}, rn = protoNames(['x', 'y', 'z', 'M'], rand), rg: Goal = {name: 'random', hyps: renameT(goal.hyps, rn)}
    const out = withWall(performance.now() + 1000, () => grow(goal, new Map(), {nodes: 0, until: performance.now() + 1000}))
    if ('tree' in out) { const rt = renameTree(out.tree, rn); expect(check(rg, rt), JSON.stringify(rg)).toBe(check(goal, out.tree)); same++; pool.push(rt); continue }
    if (!small(goal)) continue
    for (const tree of shapes(Math.min(12, leafConstraints(rg, new Map()).length))) { offered++; if (check(rg, tree)) throw new Error(`UNSOUND: ${JSON.stringify(rg)} has a model, and ${JSON.stringify(tree)} was accepted`) }
  }
  const vv = (name: string): E => ({op: 'var', name}), term = (d: number): E => {
    const r = rand(d <= 0 ? 2 : 5)
    return r === 0 ? vv(['a', 'b', 'p', 'x', 'y'][rand(5)]!) : r === 1 ? {op: 'const', value: rand(3)} : r === 2 ? {op: 'add', a: term(d - 1), b: term(d - 1)}
      : r === 3 ? {op: 'sub', a: term(d - 1), b: term(d - 1)} : {op: 'if', c: {op: 'flag', name: 'f'}, then: term(d - 1), else: term(d - 1)}
  }
  const M = (map: string, key: E): E => ({op: 'get', map, key})
  const forms: C[] = [{op: '<=', a: vv('x'), b: vv("x'")}, {op: '=', a: M("M'", vv('b')), b: M('M', vv('b'))}, {op: '=', a: M("M'", vv('b')), b: vv('b')},
    {op: '<=', a: M("M'", vv('a')), b: {op: 'add', a: M('M', vv('a')), b: vv('y')}}, {op: '<=', a: vv("y'"), b: {op: 'add', a: vv('y'), b: vv('p')}}, {op: '=', a: vv("x'"), b: vv('x')}]
  for (let t = 0; t < 12; t++) {
    const m: Machine = {name: 'random', params: ['p'], inputs: ['a', 'b'], state: {x: {op: 'const', value: 0}, y: {op: 'const', value: 0}}, maps: {M: 0},
      step: {flags: {f: {op: '<=', a: vv('a'), b: vv('x')}}, state: {x: {op: 'add', a: vv('x'), b: term(1)}, y: term(2)}, ...(rand(3) ? {maps: {M: {key: vv('a'), value: {op: 'add', a: M('M', vv('a')), b: term(1)}}}} : {})}}
    const rn = protoNames(['a', 'b', 'p', 'x', 'y', 'M', 'f'], rand), rm = renameMachine(m, rn), run = interpret(m)
    for (const then of [forms[rand(forms.length)]!, forms[rand(forms.length)]!]) {
      const sl: StepLaw = {name: 'random', then, ...(rand(4) === 0 ? {steps: 2} : {})}, rsl: StepLaw = {...sl, then: renameT(then, rn)}
      const goals = stepLawObligations(rm, [], {}, rsl)
      expect(goals).toEqual(renameGoals(stepLawObligations(m, [], {}, sl), rn))
      laws++
      const plain = withWall(performance.now() + 3000, () => proveStepLaws(m, [], [sl]))
      if (plain.proven && plain.proof) {
        const p = plain.proof, rp = {laws: {instances: {}, trees: {}}, instances: renameInstances(p.instances, rn), trees: renameTrees(p.trees, rn), ...(p.perStep ? {perStep: renamed(p.perStep, rn, i => renameInstances(i, rn))} : {})}
        expect(checkStepLaws(rm, [], [rsl], rp)).toBe(checkStepLaws(m, [], [sl], p))
        Object.values(rp.trees).forEach(tr => pool.push(tr))
        continue
      }
      if (sl.steps) continue
      // A run of the plain machine that breaks the plain law: every request (0..2) from every state reached in three steps.
      let breaks = false
      for (let p = 0; p < 3 && !breaks; p++) {
        let frontier: State[] = [run.init({p})]
        for (let depth = 0; depth < 3 && !breaks; depth++) {
          const next: State[] = []
          for (const st of frontier) for (let a = 0; a < 3; a++) for (let b = 0; b < 3; b++) {
            const after = run.step({p}, st, {a, b}), both: State = {scalars: {...st.scalars, "x'": after.scalars.x!, "y'": after.scalars.y!}, maps: {...st.maps, "M'": after.maps.M!}}
            if (!evalC(then, {p, a, b}, both, {...m, maps: {M: 0, "M'": 0}})) breaks = true
            next.push(after)
          }
          frontier = next.slice(0, 40)
        }
      }
      if (!breaks) continue
      broken++
      for (const tree of shapes(Math.min(12, leafConstraints(goals[0]!, new Map()).length))) {
        offered++
        if (checkStepLaws(rm, [], [rsl], {laws: {instances: {}, trees: {}}, instances: {}, trees: {[goals[0]!.name]: tree}})) throw new Error(`UNSOUND: ${JSON.stringify(rsl)} accepted of ${JSON.stringify(rm.step)}, broken by a run of the plain machine`)
      }
    }
  }
  console.log(`names every object has: ${same} renamed proofs checked alike, ${laws} renamed step laws built alike, ${offered} trees offered for false renamed goals and laws (${broken} laws broken by a run), none accepted`)
  covered('renamed proofs checked alike', same, 10)
  covered('renamed step laws', laws, 20)
  covered('trees offered for false renamed claims', offered, 20)
}, 300_000)
