// Tampered proofs, against real trees (the models' and the examples' laws). Two kinds:
//   - structural: a leaf's derivation broken in a way the checker's rules forbid outright (an input out of range, a row
//     combined before it exists, a multiplier that is zero, negative or fractional, a cut whose divisor doesn't divide
//     or is zero, a derivation that ends on a row with a variable left, a split on a constant, a split repeated): each
//     must be rejected, whatever the goal;
//   - semantic: the goal weakened (a hypothesis dropped, a constant moved by one, a comparison loosened) until random
//     sampling finds a model of it: then the original tree, offered for the weakened goal, must be rejected, and so must
//     anything the prover grows for it.
// This is what the mutation run (mutants.ts) leans on to see whether a change to kernel.ts or check.ts goes unnoticed.
import {expect, test} from 'bun:test'
import type {C, E, Law, Machine} from '../core/machine.ts'
import {admitFlagged, boundedLoss, capLaws, inflight, inflightLoss, loss, windowCeiling, windowLimit} from '../core/models.ts'
import type {Step} from '../core/solver.ts'
import {type Goal, type Tree, check, obligations} from './kernel.ts'
import {grow, proveLaws} from './prove.ts'

let seed = Number(process.env.FUZZ_SEED ?? 99)
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }

const strong: Law = {name: 's + 50p <= b + 150', holds: {op: '<=', a: {op: 'add', a: {op: 'var', name: 's'}, b: {op: 'mul', k: 50, a: {op: 'var', name: 'p'}}}, b: {op: 'add', a: {op: 'var', name: 'b'}, b: {op: 'const', value: 150}}}}
const subjects: [Machine, Law[]][] = [[loss(), [boundedLoss]], [inflight, [inflightLoss, strong]], [admitFlagged(), capLaws], [windowLimit(), [windowCeiling]]]
const proofs: {goal: Goal, tree: Tree}[] = []
for (const [m, laws] of subjects) {
  const r = proveLaws(m, laws)
  if (!r.proven || !r.proof) throw new Error(`${m.name}: not proven`)
  for (const g of obligations(m, laws, r.proof.instances)) proofs.push({goal: g, tree: r.proof.trees[g.name]!})
}

const leaves = (t: Tree): (Tree & {leaf: Step[]})[] => ('leaf' in t ? [t] : [...leaves(t.yes), ...leaves(t.no)])
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
  expect(tried).toBeGreaterThan(100)
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
  expect(withModel).toBeGreaterThan(30)
}, 600_000)
