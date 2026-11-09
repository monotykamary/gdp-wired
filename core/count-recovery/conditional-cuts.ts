// Untrusted conditional proof transport. No search and no lemma references enter
// the result: each prerequisite is checked independently, then inlined as a split.
import {type Goal, type LemmaCut, type Path, type Tree, canon, canonFlip, check, leafConstraintsReusing as rowsAt, lemmaPath} from '../../kernel/kernel.ts'
import {type Lin, type Step, add, k, scale} from '../solver.ts'

const alive = (until: number): boolean => performance.now() < until
const flip = (lin: Lin): Lin => add(k(1), scale(lin, -1))
const put = (path: Path, lin: Lin, holds: boolean): Path => new Map(path).set(canon(lin), {lin, holds})
const plain = (lin: Lin): boolean => Object.keys(lin).every(name => !name.includes('⟦')) && Object.values(lin).every(Number.isSafeInteger)
const decide = (lin: Lin, path: Path): boolean | undefined => {
  if (!Object.values(lin).every(Number.isSafeInteger)) return undefined
  if (Object.keys(lin).every(name => name === '1')) return (lin['1'] ?? 0) <= 0
  const direct = path.get(canon(lin))?.holds
  if (direct !== undefined) return direct
  const opposite = path.get(canonFlip(lin))?.holds
  return opposite === undefined ? undefined : !opposite
}

// Match kernel prependAtoms exactly: duplicates remain rows, and the first
// occurrence decides lookups. In particular, negcut must precede every guard.
const proofPath = (when: Lin[], cut: Lin): Path => {
  const path: Path = new Map()
  let duplicate = 0
  for (const atom of [{lin: cut, holds: false}, ...when.map(lin => ({lin, holds: true}))]) {
    const id = canon(atom.lin)
    path.set(path.has(id) ? `@${duplicate++}` : id, atom)
  }
  return path
}

function transport(source: Goal, goal: Goal, tree: Tree, from: Path, to: Path, until: number, missing?: (row: Lin) => void): Tree | undefined {
  if (!alive(until)) return undefined
  if ('split' in tree) {
    const known = decide(tree.split, to)
    if (known !== undefined) return transport(source, goal, known ? tree.yes : tree.no, put(from, tree.split, known), to, until, missing)
    const yes = transport(source, goal, tree.yes, put(from, tree.split, true), put(to, tree.split, true), until, missing)
    const no = yes && transport(source, goal, tree.no, put(from, tree.split, false), put(to, tree.split, false), until, missing)
    return yes && no ? {split: tree.split, yes, no} : undefined
  }
  const before = rowsAt(source, from), after = rowsAt(goal, to), at = new Map<string, number>()
  for (const [i, row] of after.entries()) {
    if (!alive(until)) return undefined
    // A selected cut can make a target hypothesis fold directly to false.
    // Reuse that exact input row, rather than transporting obsolete source rows.
    if (Number.isSafeInteger(row.lin['1']) && (row.lin['1'] ?? 0) > 0
      && Object.entries(row.lin).every(([name, value]) => name === '1' || value === 0)) return {leaf: [{kind: 'input', index: i}]}
    const id = canon(row.lin)
    if (!at.has(id)) at.set(id, i)
  }
  const index = (i: number): number | undefined => {
    if (!Number.isSafeInteger(i) || i < 0) return undefined
    // Squares and products follow the base rows, in the same order at both ends.
    if (i >= before.length) return i - before.length + after.length
    const row = before[i]!, found = at.get(canon(row.lin))
    if (found === undefined) missing?.(row.lin)
    return found
  }
  const leaf: Step[] = [], products: [number, number][] = []
  for (const step of tree.leaf) {
    if (!alive(until)) return undefined
    if (step.kind !== 'input') leaf.push(step)
    else {
      const i = index(step.index)
      if (i === undefined) return undefined
      leaf.push({...step, index: i})
    }
  }
  for (const [a, b] of tree.products ?? []) {
    if (!alive(until)) return undefined
    const i = index(a), j = index(b)
    if (i === undefined || j === undefined) return undefined
    products.push([i, j])
  }
  return alive(until) ? {leaf, ...(tree.products ? {products} : {}), ...(tree.squares ? {squares: tree.squares} : {})} : undefined
}

class ObservedPath extends Map<string, {lin: Lin, holds: boolean}> {
  constructor(path: Path, private readonly observed: Set<string>) { super(path) }
  override get(key: string) { this.observed.add(key); return super.get(key) }
  override has(key: string) { this.observed.add(key); return super.has(key) }
}
function dependencies(goal: Goal, tree: Tree, path: Path, facts: Set<number>, atoms: Set<string>, until: number): boolean {
  if (!alive(until)) return false
  if ('split' in tree) return dependencies(goal, tree.yes, put(path, tree.split, true), facts, atoms, until)
    && dependencies(goal, tree.no, put(path, tree.split, false), facts, atoms, until)
  const rows = rowsAt(goal, new ObservedPath(path, atoms)), values = [...path.values()]
  const observe = (i: number): void => {
    const src = rows[i]?.src
    if (src && 'fact' in src) facts.add(src.fact)
    if (src && 'atom' in src) {
      const atom = values[src.atom]
      if (atom) { atoms.add(canon(atom.lin)); atoms.add(canonFlip(atom.lin)) }
    }
  }
  for (const step of tree.leaf) {
    if (!alive(until)) return false
    if (step.kind === 'input') observe(step.index)
  }
  for (const [a, b] of tree.products ?? []) {
    if (!alive(until)) return false
    observe(a); observe(b)
  }
  return alive(until)
}

function localGoal(goal: Goal, lemma: LemmaCut): Goal | undefined {
  if (lemma.slice === undefined) return goal
  if (!lemma.slice.every(i => Number.isSafeInteger(i) && i >= 0 && i < goal.hyps.length)) return undefined
  return {...goal, hyps: lemma.slice.map(i => goal.hyps[i]!)}
}
function checked(goal: Goal, tree: Tree, path: Path, until: number): boolean {
  if (!alive(until)) return false
  try { return check(goal, tree, path) && alive(until) } catch { return false }
}

// Select prerequisites only in response to missing exact rows. Eligibility is
// evaluated against the original scope, never against another lemma's cut.
function inline(goal: Goal, source: Goal, tree: Tree, from: Path, scope: Path, base: Path, lemmas: LemmaCut[], until: number, diagnose?: (event: object) => void): Tree | undefined {
  if (!alive(until)) return undefined
  const available: LemmaCut[] = []
  for (const lemma of lemmas) {
    if (!alive(until)) return undefined
    if (plain(lemma.cut) && lemmaPath([lemma], scope) !== scope) available.push(lemma)
  }
  const required: LemmaCut[] = []
  // Already selected cuts are prepended with the kernel's duplicate semantics.
  // Their guards were tested above, not against this augmented proof context.
  const target = (cuts: LemmaCut[]): Path => lemmaPath(cuts.map(lemma => ({...lemma, when: []})), base)
  let path = base, proof: Tree | undefined
  for (;;) {
    if (!alive(until)) return undefined
    let absent: string | undefined
    path = target(required)
    proof = transport(source, goal, tree, from, path, until, row => { absent = canon(row) })
    if (proof) break
    const lemma = available.find(candidate => canon(candidate.cut) === absent && !required.includes(candidate))
    if (!lemma || !alive(until)) { diagnose?.({reason: alive(until) ? 'missing-row' : 'deadline', row: absent, available: available.length, required: required.length}); return undefined }
    const local = localGoal(goal, lemma)
    if (!local || !checked(local, lemma.tree, proofPath(lemma.when, lemma.cut), until)) return undefined
    required.push(lemma)
    required.sort((a, b) => available.indexOf(a) - available.indexOf(b))
  }
  for (let i = required.length - 1; i >= 0; i--) {
    if (!alive(until)) return undefined
    const lemma = required[i]!, prefix = target(required.slice(0, i)), known = decide(lemma.cut, prefix)
    const local = localGoal(goal, lemma)
    if (!local) return undefined
    if (known === true) proof = transport(goal, goal, proof, path, prefix, until)
    else {
      const no = transport(local, goal, lemma.tree, proofPath(lemma.when, lemma.cut), known === false ? prefix : put(prefix, lemma.cut, false), until)
      if (!no) return undefined
      if (known === false) proof = no
      else {
        const yes = transport(goal, goal, proof, path, put(prefix, lemma.cut, true), until)
        if (!yes) return undefined
        proof = {split: lemma.cut, yes, no}
      }
    }
    if (!proof) return undefined
    path = prefix
  }
  return alive(until) ? proof : undefined
}

/** Transport a refutation to negcut + scope, inline required prior cuts, then
 * minimize its guards and containing-goal hypothesis slice. `until` is an
 * absolute performance.now() deadline, independent of the prover's clock. */
function admitCut(goal: Goal, source: Goal, tree: Tree, from: Path, scope: Path, cut: Lin, available: LemmaCut[], until: number): LemmaCut | undefined {
  if (!alive(until) || !plain(cut)) return undefined
  let when: Lin[] = []
  for (const atom of scope.values()) {
    if (!alive(until)) return undefined
    when.push(atom.holds ? atom.lin : flip(atom.lin))
  }
  let base = proofPath(when, cut), proof = inline(goal, source, tree, from, scope, base, available, until)
  if (!proof) return undefined
  const facts = new Set<number>(), atoms = new Set<string>()
  if (!dependencies(goal, proof, base, facts, atoms, until)) return undefined
  let slice = [...facts].sort((a, b) => a - b), small = {...goal, hyps: slice.map(i => goal.hyps[i]!)}
  const narrowed = transport(goal, small, proof, base, base, until)
  if (narrowed) proof = narrowed
  else { slice = goal.hyps.map((_, i) => i); small = goal }
  const less = when.filter(lin => atoms.has(canon(lin)) || atoms.has(canonFlip(lin)))
  if (less.length < when.length) {
    const next = proofPath(less, cut), reduced = transport(small, small, proof, base, next, until)
    if (reduced) { when = less; base = next; proof = reduced }
  }
  // Lookup traces are conservative; each further removal must transport exactly.
  for (let i = when.length - 1; i >= 0; i--) {
    if (!alive(until)) return undefined
    const less = when.filter((_, j) => j !== i), next = proofPath(less, cut)
    const reduced = transport(small, small, proof, base, next, until)
    if (reduced) { when = less; base = next; proof = reduced }
  }
  return checked(small, proof, base, until) ? {when, cut, tree: proof, slice} : undefined
}

// Use original hypotheses only, but avoid rebuilding unrelated count-instance
// rows at every source-proof leaf. Exact transport and the final checker remain
// authoritative; a missed syntactic match falls back to the full goal.
const hypothesisIndex = new WeakMap<Goal, Map<string, Set<number>>>()
function relevantHypotheses(goal: Goal, source: Goal, tree: Tree, path: Path, available: LemmaCut[], until: number): number[] | undefined {
  const used = new Set<number>()
  if (!dependencies(source, tree, path, used, new Set(), until)) return undefined
  let index = hypothesisIndex.get(goal)
  if (!index) {
    index = new Map()
    const visit = (value: Goal['hyps'][number], owner: number): boolean => {
      if (!alive(until)) return false
      const key = JSON.stringify(value), owners = index!.get(key) ?? new Set<number>()
      owners.add(owner); index!.set(key, owners)
      if (value.op === 'and' || value.op === 'or') return value.xs.every(c => visit(c, owner))
      return value.op !== 'not' || visit(value.x, owner)
    }
    if (!goal.hyps.every(visit)) return undefined
    hypothesisIndex.set(goal, index)
  }
  const selected = new Set<number>()
  for (const i of used) for (const j of index.get(JSON.stringify(source.hyps[i])) ?? []) selected.add(j)
  for (const lemma of available) {
    if (lemma.slice === undefined || lemma.slice.some(i => !Number.isSafeInteger(i) || i < 0 || i >= goal.hyps.length)) return undefined
    for (const i of lemma.slice) selected.add(i)
  }
  return [...selected].sort((a, b) => a - b)
}
export function admitConditionalCut(goal: Goal, source: Goal, tree: Tree, from: Path, scope: Path, cut: Lin, available: LemmaCut[], until: number): LemmaCut | undefined {
  if (!alive(until) || !plain(cut)) return undefined
  const slice = relevantHypotheses(goal, source, tree, from, available, until)
  if (slice && slice.length < goal.hyps.length) {
    const positions = new Map(slice.map((old, index) => [old, index])), small = {...goal, hyps: slice.map(i => goal.hyps[i]!)}
    const local = available.map(lemma => ({...lemma, slice: lemma.slice!.map(i => positions.get(i)!)}))
    const result = admitCut(small, source, tree, from, scope, cut, local, until)
    if (result) return {...result, slice: (result.slice ?? small.hyps.map((_, i) => i)).map(i => slice[i]!)}
  }
  return admitCut(goal, source, tree, from, scope, cut, available, until)
}

/** Emit an ordinary tree at scope, inlining only active cuts whose exact rows
 * the source proof needs. The returned tree is kernel-checked without lemmas. */
export function inlineConditionalCuts(goal: Goal, source: Goal, tree: Tree, from: Path, scope: Path, lemmas: LemmaCut[], until: number, diagnose?: (event: object) => void): Tree | undefined {
  const begun = performance.now(), proof = inline(goal, source, tree, from, scope, scope, lemmas, until, diagnose)
  const accepted = !!proof && checked(goal, proof, scope, until)
  diagnose?.({reason: accepted ? 'complete' : alive(until) ? proof ? 'check-failed' : 'transport-failed' : 'deadline', proposed: !!proof, checked: accepted, wallMs: performance.now() - begun})
  return accepted ? proof : undefined
}
