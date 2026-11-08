// Untrusted proof compression. Turn repeated forced splits into independently checked conditional cuts.
// No search, protocol vocabulary, new facts or proof-budget changes: failed transport/check returns no proposal.
import {type C, type E, n, plus, times, x} from './machine.ts'
import {type Lin, type Step, add, k, scale} from './solver.ts'
import {type Goal, type LemmaCut, type Path, type Tree, canon, canonFlip, checkGoalLemmas, isCell, isMonomial, leafConstraintsReusing as leafConstraints, lemmaPath} from '../kernel/kernel.ts'

type Leaf = Extract<Tree, {leaf: Step[]}>
export type ProofOrigin = {goal: Goal, tree: Tree, path: Path}
const originOf = new WeakMap<Tree, ProofOrigin>()
// Search provenance is only an optional proposer hint. The trusted checker never reads this cache.
export const proofOrigins = {enabled: false}
export const proofOrigin = (tree: Tree): ProofOrigin | undefined => originOf.get(tree)
export const setProofOrigin = (tree: Tree, origin: ProofOrigin): void => { originOf.set(tree, origin) }
export function rememberProofOrigin(out: Tree | undefined, part: Goal, tree: Tree, path: Path, whole: Goal): void {
  if (!out) return
  const earlier = originOf.get(tree)
  if (earlier && earlier.goal.hyps.length <= part.hyps.length) originOf.set(out, earlier)
  else if (part.hyps.length < whole.hyps.length) originOf.set(out, {goal: part, tree, path: new Map(path)})
}

type ProofRows = ReturnType<typeof leafConstraints>
const rowIds = new WeakMap<Lin, string>(), rowIndexes = new WeakMap<ProofRows, Map<string, number>>()
const rowId = (lin: Lin): string => {
  let id = rowIds.get(lin)
  if (id === undefined) { id = canon(lin); rowIds.set(lin, id) }
  return id
}
const rowIndex = (rows: ProofRows): Map<string, number> => {
  let at = rowIndexes.get(rows)
  if (!at) { at = new Map(); rows.forEach((r, i) => { const id = rowId(r.lin); if (!at!.has(id)) at!.set(id, i) }); rowIndexes.set(rows, at) }
  return at
}
const rowsOf = new WeakMap<Tree, {goal: Goal, path: string, rows: ProofRows, atoms?: Set<string>}>()
const pathKey = (p: Path): string => JSON.stringify([...p].map(([id, a]) => [id, canon(a.lin), a.holds]))
const savedProofRows = (tree: Tree, goal: Goal, path: Path) => {
  const old = rowsOf.get(tree)
  return old?.goal === goal && old.path === pathKey(path) ? old : undefined
}
const saveProofRows = (tree: Tree, goal: Goal, path: Path, rows: ProofRows, atoms?: Set<string>): void => {
  rowsOf.set(tree, {goal, path: pathKey(path), rows, atoms})
}
// Hints only: the trusted checker always rebuilds its own rows. Capturing reuses work already done by widen.
export function rememberProofRows(tree: Tree, goal: Goal, path: Path, rows: ProofRows): void {
  if (proofOrigins.enabled && 'leaf' in tree) saveProofRows(tree, goal, path, rows)
}

type Branch = Extract<Tree, {split: Lin}>
const decide = (lin: Lin, path: Path): boolean | undefined => {
  if (!Object.values(lin).every(Number.isSafeInteger)) return undefined
  if (Object.keys(lin).every(k => k === '1')) return (lin['1'] ?? 0) <= 0
  const direct = path.get(canon(lin))?.holds
  if (direct !== undefined) return direct
  const opposite = path.get(canonFlip(lin))?.holds
  return opposite === undefined ? undefined : !opposite
}
const flip = (r: Lin) => add(k(1), scale(r, -1))
const put = (p: Path, lin: Lin, holds: boolean): Path => new Map(p).set(canon(lin), {lin, holds})
const proofPath = (when: Lin[], cut: Lin): Path => {
  const p: Path = new Map()
  let duplicate = 0
  for (const atom of [{lin: cut, holds: false}, ...when.map(lin => ({lin, holds: true}))]) {
    const key = canon(atom.lin)
    p.set(p.has(key) ? `@${duplicate++}` : key, atom)
  }
  return p
}

// Unlike widen, transport never calls a solver when a row is missing.
function transport(from: Goal, to: Goal, tree: Tree, before: Path, after: Path, until: number, missing?: (row: Lin) => void): Tree | undefined {
  if (performance.now() >= until) return undefined
  if ('split' in tree) {
    const known = decide(tree.split, after)
    if (known !== undefined) return transport(from, to, known ? tree.yes : tree.no, put(before, tree.split, known), after, until, missing)
    const yes = transport(from, to, tree.yes, put(before, tree.split, true), put(after, tree.split, true), until, missing)
    const no = yes && transport(from, to, tree.no, put(before, tree.split, false), put(after, tree.split, false), until, missing)
    return yes && no ? {split: tree.split, yes, no} : undefined
  }
  const atoms = new Set<string>()
  const old = savedProofRows(tree, from, before)?.rows ?? leafConstraints(from, before)
  const rows = leafConstraints(to, new ObservedPath(after, atoms)), at = rowIndex(rows)
  const index = (i: number): number | undefined => {
    if (i >= old.length) return i - old.length + rows.length
    const row = old[i], found = row && at.get(rowId(row.lin))
    if (row && found === undefined) missing?.(row.lin)
    return found
  }
  const leaf: Step[] = [], products: [number, number][] = []
  for (const s of tree.leaf) {
    if (s.kind !== 'input') leaf.push(s)
    else { const i = index(s.index); if (i === undefined) return undefined; leaf.push({...s, index: i}) }
  }
  for (const [a, b] of tree.products ?? []) {
    const i = index(a), j = index(b)
    if (i === undefined || j === undefined) return undefined
    products.push([i, j])
  }
  const out = {leaf, ...(tree.products ? {products} : {}), ...(tree.squares ? {squares: tree.squares} : {})}
  saveProofRows(out, to, after, rows, atoms)
  return out
}

// Observe only lookups; enumerating path rows is not itself a dependence on every path assumption.
class ObservedPath extends Map<string, {lin: Lin, holds: boolean}> {
  constructor(path: Path, private readonly observed: Set<string>) { super(path) }
  override get(key: string) { this.observed.add(key); return super.get(key) }
  override has(key: string) { this.observed.add(key); return super.has(key) }
}
function dependencies(g: Goal, t: Tree, path: Path, facts: Set<number>, atoms: Set<string>, until: number): boolean {
  if (performance.now() >= until) return false
  if ('split' in t) return dependencies(g, t.yes, put(path, t.split, true), facts, atoms, until)
    && dependencies(g, t.no, put(path, t.split, false), facts, atoms, until)
  const observed = new ObservedPath(path, atoms), cached = savedProofRows(t, g, path)
  const rows = cached?.rows ?? leafConstraints(g, observed), values = [...path.values()]
  if (cached?.atoms) for (const key of cached.atoms) atoms.add(key)
  // Prover-captured tables have no new lookup trace. Conservatively retain their source conditions.
  else if (cached) for (const a of values) { atoms.add(canon(a.lin)); atoms.add(canonFlip(a.lin)) }
  for (const i of [...t.leaf.flatMap(s => s.kind === 'input' ? [s.index] : []), ...(t.products ?? []).flat()]) {
    const src = rows[i]?.src
    if (src && 'fact' in src) facts.add(src.fact)
    if (src && 'atom' in src) {
      const a = values[src.atom]
      if (a) { atoms.add(canon(a.lin)); atoms.add(canonFlip(a.lin)) }
    }
  }
  return true
}

// Conditional replay scopes are explicit hypotheses, never silently assumed. Root scopes currently reify scalar
// rows; rootless production certificates also support all the original cell/term/monomial columns.
function scopeCondition(lin: Lin): C | undefined {
  let a: E = n(0), b: E = n(0)
  for (const [name, z] of Object.entries(lin)) {
    if (!Number.isSafeInteger(z)) return undefined
    if (name !== '1' && (isCell(name) || isMonomial(name) || name.startsWith('⟦'))) return undefined
    const term = name === '1' ? n(Math.abs(z)) : times(Math.abs(z), x(name))
    if (z > 0) a = plus(a, term); else if (z < 0) b = plus(b, term)
  }
  return {op: '<=', a, b}
}

export type SharedCuts = {goal: Goal, tree: Tree, lemmas: LemmaCut[], stats: {before: number, after: number, cuts: number, sourceHyps: number, lemmaHyps: number, mainNodes: number, checkMs: number, buildMs: number}}
// Candidate construction only. Call shareLemmaCuts or the containing machine checker before admission.
export function proposeLemmaCuts(goal: Goal, tree: Tree, options: {path?: Path, until?: number, minNodes?: number, minimizeConditions?: boolean, trace?: (event: Record<string, string | number | boolean>) => void} = {}): SharedCuts | undefined {
  const started = performance.now(), root = options.path ?? new Map(), until = options.until ?? Infinity
  const sizes = new WeakMap<Tree, number>(), repeats = new Map<string, number>()
  const measure = (t: Tree): number => {
    if ('leaf' in t) { sizes.set(t, 1); return 1 }
    const id = canon(t.split); repeats.set(id, (repeats.get(id) ?? 0) + 1)
    const size = 1 + measure(t.yes) + measure(t.no); sizes.set(t, size); return size
  }
  const before = measure(tree)
  if (before < (options.minNodes ?? 64)) return undefined
  const roots = [...root.values()], conditions = roots.map(a => scopeCondition(a.holds ? a.lin : flip(a.lin)))
  if (conditions.some(c => !c)) return undefined
  const scoped = root.size ? {...goal, hyps: [...goal.hyps, ...conditions as C[]]} : goal
  const lemmas: LemmaCut[] = [], shared = new Map<string, number>(), origins = new WeakMap<Tree, {tree: Leaf, path: Path}>()
  const keyOf = (when: Lin[], cut: Lin) => when.map(canon).sort().join(';') + '=>' + canon(cut)
  const makeLemma = (t: Branch, original: Path, real: Path): LemmaCut | undefined => {
    let when = [...real.values()].map(a => a.holds ? a.lin : flip(a.lin))
    let base = proofPath(when, t.split)
    const available = lemmas.filter(l => l.when.every(w => decide(w, real) === true))
    const from = (g: Goal, body: Tree, path: Path): Tree | undefined => {
      const required: LemmaCut[] = []
      let proof: Tree | undefined
      for (;;) {
        let absent: string | undefined
        const target = required.reduce((p, l) => put(p, l.cut, true), base)
        proof = transport(g, goal, body, path, target, until, row => { absent = canon(row) })
        if (proof) break
        const dependency = available.find(l => canon(l.cut) === absent && !required.includes(l))
        if (!dependency) return undefined
        required.push(dependency)
      }
      // Inline only prerequisites whose exact rows were needed. Each is an already independent proof;
      // no certificate lemma is permitted to cite another lemma, and there is no circular trust.
      for (let i = required.length - 1; i >= 0; i--) {
        const l = required[i]!, local = l.slice ? {...goal, hyps: l.slice.map(j => goal.hyps[j]!)} : goal
        const prefix = required.slice(0, i).reduce((p, prev) => put(p, prev.cut, true), base)
        const no = transport(local, goal, l.tree, proofPath(l.when, l.cut), put(prefix, l.cut, false), until)
        if (!no) return undefined
        proof = {split: l.cut, yes: proof, no}
      }
      return proof
    }
    const origin = proofOrigin(t.no)
    let proof = origin && from(origin.goal, origin.tree, origin.path)
    proof ??= from(goal, t.no, put(original, t.split, false))
    if (!proof) return undefined
    const used = new Set<number>(), seen = new Set<string>()
    if (!dependencies(goal, proof, base, used, seen, until)) return undefined
    let slice = [...used].sort((a, b) => a - b), small = {...goal, hyps: slice.map(i => goal.hyps[i]!)}
    const narrowed = transport(goal, small, proof, base, base, until)
    if (narrowed) proof = narrowed
    else { slice = goal.hyps.map((_, i) => i); small = goal }
    // A failed dependency minimization is just a missed optimization. The old proof and full conditions remain.
    const needed = new Set<string>()
    if (!dependencies(small, proof, base, new Set(), needed, until)) return undefined
    const less = when.filter(w => needed.has(canon(w)) || needed.has(canonFlip(w)))
    if (less.length < when.length) {
      const next = proofPath(less, t.split), reduced = transport(small, small, proof, base, next, until)
      if (reduced) { when = less; base = next; proof = reduced }
    }
    // Lookup traces are conservative (a discarded alternative may read a condition). Remove each remaining
    // unnecessary condition by exact row transport, never by asserting that an unknown condition holds.
    for (let i = options.minimizeConditions ? when.length - 1 : -1; i >= 0; i--) {
      const less = when.filter((_, j) => i !== j), next = proofPath(less, t.split)
      const reduced = transport(small, small, proof, base, next, until)
      if (reduced) { when = less; base = next; proof = reduced }
    }
    return {when, cut: t.split, tree: proof, slice}
  }
  const visit = (t: Tree, original: Path, real: Path): Tree | undefined => {
    if (performance.now() >= until) return undefined
    if ('leaf' in t) { const copy = {...t}; origins.set(copy, {tree: t, path: original}); return copy }
    const id = canon(t.split)
    // Prefer compact repeated derivations. Larger enclosing candidates are left as ordinary tree nodes;
    // the final comparison still weighs each proposed proof by its actual hypothesis context.
    if ((repeats.get(id) ?? 0) >= 2 && (sizes.get(t.no) ?? 0) >= 3 && (sizes.get(t.no) ?? 0) <= 128) {
      const fullKey = keyOf([...real.values()].map(a => a.holds ? a.lin : flip(a.lin)), t.split)
      let found = shared.get(fullKey)
      if (found === undefined) {
        const usable = lemmas.findIndex(l => canon(l.cut) === id && l.when.every(w => decide(w, real) === true))
        if (usable >= 0) found = usable
      }
      if (found === undefined) {
        const begun = performance.now(), lemma = makeLemma(t, original, real)
        options.trace?.({stage: 'lemma', produced: !!lemma, nodes: sizes.get(t.no) ?? 0, ms: performance.now() - begun, when: lemma?.when.length ?? -1, hyps: lemma?.slice?.length ?? -1})
        if (lemma) {
          const key = keyOf(lemma.when, lemma.cut)
          found = shared.get(key)
          if (found === undefined) { found = lemmas.length; lemmas.push(lemma); shared.set(key, found) }
        }
      }
      if (found !== undefined) {
        shared.set(fullKey, found)
        return visit(t.yes, put(original, t.split, true), real)
      }
    }
    const yes = visit(t.yes, put(original, t.split, true), put(real, t.split, true))
    const no = yes && visit(t.no, put(original, t.split, false), put(real, t.split, false))
    return yes && no ? {split: t.split, yes, no} : undefined
  }
  const skeleton = visit(tree, root, root)
  if (!skeleton || !lemmas.length) { options.trace?.({stage: 'no-skeleton', lemmas: lemmas.length}); return undefined }
  const finish = (t: Tree, path: Path): Tree | undefined => {
    if ('leaf' in t) { const src = origins.get(t)!; return transport(goal, scoped, src.tree, src.path, lemmaPath(lemmas, path), until) }
    const yes = finish(t.yes, put(path, t.split, true)), no = yes && finish(t.no, put(path, t.split, false))
    return yes && no ? {split: t.split, yes, no} : undefined
  }
  let out = finish(skeleton, root)
  if (!out) return undefined
  // Prove the other side of each explicit scope condition by its contradictory hypothesis.
  for (let i = roots.length - 1; i >= 0; i--) {
    const a = roots[i]!, prefix: Path = new Map([...root].slice(0, i)), bad = put(prefix, a.lin, !a.holds)
    const rows = leafConstraints(scoped, bad), absurd = rows.findIndex(r => Object.keys(r.lin).every(k => k === '1') && (r.lin['1'] ?? 0) > 0)
    let opposite: Tree
    if (absurd >= 0) opposite = {leaf: [{kind: 'input', index: absurd}]}
    else {
      const left = rows.findIndex(r => canon(r.lin) === canon(a.lin)), right = rows.findIndex(r => canon(r.lin) === canon(flip(a.lin)))
      if (left < 0 || right < 0) return undefined
      opposite = {leaf: [{kind: 'input', index: left}, {kind: 'input', index: right}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]}
    }
    out = a.holds ? {split: a.lin, yes: out, no: opposite} : {split: a.lin, yes: opposite, no: out}
  }
  const count = (t: Tree): number => 'leaf' in t ? 1 : 1 + count(t.yes) + count(t.no)
  const after = count(out) + lemmas.reduce((n, l) => n + count(l.tree), 0)
  const workBefore = before * Math.max(1, goal.hyps.length), workAfter = count(out) * Math.max(1, scoped.hyps.length) + lemmas.reduce((n, l) => n + count(l.tree) * Math.max(1, l.slice?.length ?? scoped.hyps.length), 0)
  if (workAfter >= workBefore || performance.now() >= until) { options.trace?.({stage: 'not-cheaper-or-expired', before, after, workBefore, workAfter}); return undefined }
  return {goal: scoped, tree: out, lemmas, stats: {before, after, cuts: lemmas.length, sourceHyps: goal.hyps.length, lemmaHyps: lemmas.reduce((n, l) => n + (l.slice?.length ?? scoped.hyps.length), 0), mainNodes: count(out), checkMs: 0, buildMs: performance.now() - started}}
}

export function shareLemmaCuts(goal: Goal, tree: Tree, options: Parameters<typeof proposeLemmaCuts>[2] = {}): SharedCuts | undefined {
  const proposed = proposeLemmaCuts(goal, tree, options)
  if (!proposed) return undefined
  const start = performance.now(), checked = checkGoalLemmas(proposed.goal, proposed.tree, proposed.lemmas)
  if (!checked) { options?.trace?.({stage: 'kernel-rejected'}); return undefined }
  proposed.stats.checkMs = performance.now() - start
  return proposed
}
