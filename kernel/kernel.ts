// The kernel: the only part of a machine proof that is trusted, besides check.ts. Provers (prove.ts, or anything else)
// are untrusted; they hand the kernel a proof tree and the kernel either accepts it or doesn't.
//
// A goal is a list of hypotheses over naturals (quantifier-free: +, ∸, × by a constant, min, max, if, map reads) that
// can't all hold. A proof is a tree of splits on linear atoms (lin <= 0, or lin >= 1), with a derivation at each leaf.
// At a leaf, the kernel takes the path's atoms, every linear fact the hypotheses give under the path (a comparison whose
// ifs, mins and truncations the path decides; the parts of a conjunction; the one disjunct left when the path refutes
// the others), each variable >= 0, and, for two reads of one map at keys the path proves equal, their equality; the
// leaf's derivation must refute them (check.ts). Splits are trivially exhaustive, so a tree whose leaves all check
// means the hypotheses never hold together.
//
// Machines: `obligations` turns a machine and a set of laws into goals, the induction rule spelled out: each law holds
// at the start, and one step from a state where every law in the set holds keeps it. A law that holds at every key is
// assumed at whatever keys the proof names (instantiating ∀ is sound at any term) and is proven at a fresh key. The
// whole set is checked, so nothing is assumed that isn't proven.
//
// Two kinds of assumption: `pre`, about the params alone, is a precondition (the law is claimed only for params that
// meet it), so it holds at the start and at every step; `assume`, about each request, holds only at a step, since no
// request has come at the start.
import {checkRefutation} from '../core/check.ts'
import type {C, E, Law, Machine, MapUpdate} from '../core/machine.ts'
import {type Constraint, type Lin, type Step, add, k, scale, sub, v} from '../core/solver.ts'

// An exhaustive switch's default: TypeScript proves it unreachable, and if it is reached anyway (a value from outside
// the types), it fails loudly instead of returning undefined.
export function unreachable(value: never): never { throw new Error(`unhandled case: ${JSON.stringify(value)}`) }

export type Tree = {split: Lin, yes: Tree, no: Tree} | {leaf: Step[], products?: [number, number][], squares?: Lin[]}
export type Goal = {name: string, hyps: C[]}

// The path: atoms decided so far, by their canonical text. yes: lin <= 0; no: lin >= 1.
export type Path = Map<string, {lin: Lin, holds: boolean}>
// (Remembered per linear form: a form is never changed once built, and the same forms are looked up at every node.)
const canonMemo = new WeakMap<Lin, string>(), flipMemo = new WeakMap<Lin, string>()
export const canon = (lin: Lin): string => {
  let out = canonMemo.get(lin)
  if (out === undefined) canonMemo.set(lin, (out = Object.keys(lin).sort().map(key => `${key}:${lin[key]}`).join(',')))
  return out
}
// canon(1 − lin), the atom that decides lin <= 0 the other way, without building it.
export const canonFlip = (lin: Lin): string => {
  let out = flipMemo.get(lin)
  if (out !== undefined) return out
  const keys = Object.keys(lin)
  if (!('1' in lin)) keys.push('1')
  const parts: string[] = []
  for (const key of keys.sort()) { const c = key === '1' ? 1 - (lin['1'] ?? 0) : -lin[key]!; if (c !== 0) parts.push(`${key}:${c}`) }
  flipMemo.set(lin, (out = parts.join(',')))
  return out
}
export const atomOf = (lin: Lin, holds: boolean): Constraint => ({lin: holds ? lin : add(k(1), scale(lin, -1)), label: ''})

// Is lin <= 0 decided by the path? A constant atom decides itself.
// Over the integers lin <= 0 fails exactly when 1 - lin <= 0 holds, so either atom decides the other.
function decide(lin: Lin, path: Path): boolean | undefined {
  let constant = true
  for (const key in lin) if (key !== '1') { constant = false; break }
  if (constant) return (lin['1'] ?? 0) <= 0
  const direct = look(path, canon(lin))
  if (direct !== undefined) return direct
  const flipped = look(path, canonFlip(lin))
  return flipped === undefined ? undefined : !flipped
}
// Every decision a hypothesis' facts read, found or not, while they are recorded (leafConstraintsReusing).
let recording: Map<string, boolean | undefined> | undefined
const look = (path: Path, key: string): boolean | undefined => { const out = path.get(key)?.holds; if (recording) recording.set(key, out); return out }

// A term's linear form under the path. Reads become cells, named by map and key: `M[key]`; a choice the path leaves
// open (∸, min, max, if) becomes a column of its own, `⟦n⟧`, standing for the term's value (see termRows).
// Remembered per path and term (a path is never changed once built; a new decision is a new path), so a term shared
// across hypotheses, or nested in a k-step run's later states, is read once per path.
// A term without a choice (no ∸, min, max or if inside, its keys' too) reads alike on every path: remembered once.
const linearMemo = new WeakMap<Path, WeakMap<E, Lin | undefined>>()
const freeMemo = new WeakMap<E, boolean>(), freeLinear = new WeakMap<E, Lin | undefined>()
const choiceFree = (e: E): boolean => {
  let out = freeMemo.get(e)
  if (out !== undefined) return out
  switch (e.op) {
    case 'var': case 'const': out = true; break
    case 'mul': out = choiceFree(e.a); break
    case 'get': out = choiceFree(e.key); break
    case 'add': case 'prod': out = choiceFree(e.a) && choiceFree(e.b); break
    case 'sub': case 'min': case 'max': case 'if': out = false; break
  }
  freeMemo.set(e, out)
  return out
}
export function linear(e: E, path: Path): Lin | undefined {
  if (choiceFree(e)) {
    if (freeLinear.has(e)) return freeLinear.get(e)
    const out = linearOf(e, path)
    freeLinear.set(e, out)
    return out
  }
  if (reuse) return reusing(seenOf(linearSeen, e), path, p => linearOf(e, p))
  let memo = linearMemo.get(path)
  if (!memo) linearMemo.set(path, (memo = new WeakMap()))
  if (memo.has(e)) return memo.get(e)
  const out = linearOf(e, path)
  memo.set(e, out)
  return out
}
function linearOf(e: E, path: Path): Lin | undefined {
  switch (e.op) {
    case 'var': return e.name === '1' || /[*[\],:⟦]/.test(e.name) ? undefined : v(e.name) // those characters build cells, monomials and term columns
    case 'const': return k(e.value)
    case 'mul': { const a = linear(e.a, path); return a && scale(a, e.k) }
    case 'prod': { const a = linear(e.a, path), b = linear(e.b, path); return a && b && times(a, b) }
    case 'add': { const a = linear(e.a, path), b = linear(e.b, path); return a && b && add(a, b) }
    case 'sub': case 'min': case 'max': {
      const a = linear(e.a, path), b = linear(e.b, path)
      if (!a || !b) return undefined
      const aLeB = decide(sub(a, b), path), bLeA = decide(sub(b, a), path)
      if (e.op === 'sub') return bLeA === true ? sub(a, b) : bLeA === false ? k(0) : v(termColumn(e))
      if (aLeB === undefined) return v(termColumn(e))
      return (e.op === 'min') === aLeB ? a : b
    }
    case 'if': { const c = truth(e.c, path); return c === undefined ? v(termColumn(e)) : linear(c ? e.then : e.else, path) }
    case 'get': { const key = linear(e.key, path); return key && v(`${e.map}[${canon(key)}]`) }
  }
}

// --- term columns -------------------------------------------------------------------------------------------------------
// A choice the path leaves open is a column ⟦n⟧ for the n-th term met (one table per process: the name only has to be
// the same for the same term). A leaf reads it through rows that hold whichever way the choice goes (termRows), so a
// fact about the choice's value can be split on, and proven, before the choice is decided.
// Terms are hash-consed: a term's id comes from its operator, its fields and its parts' ids, remembered per object, so a
// deep term (a k-step run nests k steps) is read once, not once per lookup.
const termIds = new Map<string, number>(), termTable: (E | C)[] = [], memo = new WeakMap<object, number>()
function termId(t: E | C): number {
  const had = memo.get(t)
  if (had !== undefined) return had
  const parts = Object.entries(t).sort(([x], [y]) => (x < y ? -1 : x > y ? 1 : 0)).map(([key, val]) => (Array.isArray(val) ? `${key}=[${val.map(x => termId(x as E | C)).join(',')}]` : typeof val === 'object' && val !== null ? `${key}=#${termId(val as E | C)}` : `${key}=${JSON.stringify(val)}`))
  const key = parts.join(';')
  let id = termIds.get(key)
  if (id === undefined) { id = termTable.length; termIds.set(key, id); termTable.push(t) }
  memo.set(t, id)
  return id
}
export const termColumn = (e: E): string => `⟦${termId(e)}⟧`
export const columnTerm = (name: string): E | undefined => { const m = /^⟦(\d+)⟧$/.exec(name); return m ? termTable[Number(m[1])] as E : undefined }
// Whether the path decides a choice's top (an if's condition, which side of min, max or ∸).
export function decided(e: E, path: Path): boolean {
  if (e.op === 'if') return truth(e.c, path) !== undefined
  if (e.op !== 'sub' && e.op !== 'min' && e.op !== 'max') return true
  const a = linear(e.a, path), b = linear(e.b, path)
  return !!a && !!b && decide(e.op === 'sub' ? sub(b, a) : sub(a, b), path) !== undefined
}
// The rows a term column brings: its bounds, true whichever way the choice goes (min(a, b) ≤ a and ≤ b; max(a, b) ≥ a
// and ≥ b; a ∸ b ≥ a − b and ≤ a), and, once the path decides it, its equality to the branch taken.
export function termRows(name: string, path: Path): Lin[] {
  const e = columnTerm(name)!, col = v(name), out: Lin[] = []
  if (e.op === 'min' || e.op === 'max' || e.op === 'sub') {
    const a = linear(e.a, path), b = linear(e.b, path)
    if (a && b) {
      if (e.op === 'min') out.push(sub(col, a), sub(col, b))
      if (e.op === 'max') out.push(sub(a, col), sub(b, col))
      if (e.op === 'sub') out.push(sub(sub(a, b), col), sub(col, a))
    }
  }
  // An if is one of its two naturals, so at most their sum, whichever way its condition goes (a yes/no's if(c, 1, 0)
  // is at most 1 without deciding c). Only over constant branches: over a variable one (a map's if(c, Given[k], 0)),
  // each such row is one more in every leaf and slows the solve more than it saves.
  if (e.op === 'if') {
    const a = linear(e.then, path), b = linear(e.else, path), constant = (l: Lin) => Object.entries(l).every(([key, c]) => key === '1' || c === 0)
    if (a && b && constant(a) && constant(b)) out.push(sub(col, add(a, b)))
  }
  if (decided(e, path)) { const r = linear(e, path); if (r) out.push(sub(col, r), sub(r, col)) }
  return out
}

// Products: multiply out, each monomial (its factors joined by '*', sorted) one more natural variable. A factor is a
// variable or a map's cell (used ≤ per·Seats[k] reads one); an open choice isn't (the path decides it first, and the
// product is of its branch). Forgetting how monomials relate (x*x to x, say, or two monomials over cells the path
// proves equal) only weakens what a leaf may use, so it stays sound; distributing is what proves spend <= m·count over
// a node from the same law at its children.
function times(a: Lin, b: Lin): Lin | undefined {
  const out: Lin[] = []
  for (const [p, cp] of Object.entries(a)) for (const [q, cq] of Object.entries(b)) {
    if (p.includes('⟦') || q.includes('⟦')) return undefined
    const fs = [...(p === '1' ? [] : factorsOf(p)), ...(q === '1' ? [] : factorsOf(q))].sort()
    out.push({[fs.length ? fs.join('*') : '1']: cp * cq})
  }
  return add(...out)
}
// A name's factors: split at each '*' outside a cell's brackets (a cell's key may itself read a monomial).
const factorMemo = new Map<string, string[]>()
export function factorsOf(name: string): string[] {
  let out = factorMemo.get(name)
  if (out) return out
  out = []
  let depth = 0, start = 0
  for (let i = 0; i <= name.length; i++) {
    const ch = name[i]
    if (ch === '[') depth++
    else if (ch === ']') depth--
    else if ((ch === '*' && depth === 0) || i === name.length) { out.push(name.slice(start, i)); start = i + 1 }
  }
  factorMemo.set(name, out)
  return out
}
export const isMonomial = (name: string) => factorsOf(name).length > 1
export const isCell = (name: string) => name.includes('[') && !isMonomial(name)

// The atoms (lin <= 0 each) that make a comparison true, and those that make it false (one of which holds).
// Remembered per path and comparison (as linear is), and once for a comparison of terms without choices.
type Comparison = {when: Lin[], unless: Lin[][]} | undefined
const comparisonMemo = new WeakMap<Path, WeakMap<C, Comparison>>(), freeComparison = new WeakMap<C, Comparison>()
function comparison(c: Extract<C, {a: E}>, path: Path): Comparison {
  const free = choiceFree(c.a) && choiceFree(c.b)
  if (free && freeComparison.has(c)) return freeComparison.get(c)
  if (!free && reuse) return reusing(seenOf(comparisonSeen, c), path, p => comparisonOf(c, p))
  let memo = comparisonMemo.get(path)
  if (!free) {
    if (!memo) comparisonMemo.set(path, (memo = new WeakMap()))
    if (memo.has(c)) return memo.get(c)
  }
  const out = comparisonOf(c, path)
  if (free) freeComparison.set(c, out); else memo!.set(c, out)
  return out
}
function comparisonOf(c: Extract<C, {a: E}>, path: Path): Comparison {
  const a = linear(c.a, path), b = linear(c.b, path)
  if (!a || !b) return undefined
  const ab = sub(a, b), ba = sub(b, a)
  if (c.op === '<=') return {when: [ab], unless: [[add(ba, k(1))]]}
  if (c.op === '<') return {when: [add(ab, k(1))], unless: [[ba]]}
  return {when: [ab, ba], unless: [[add(ab, k(1))], [add(ba, k(1))]]}
}

// Kleene truth under the path: true, false, or undefined when open (remembered per path and condition).
const truthMemo = new WeakMap<Path, WeakMap<C, boolean | undefined>>()
export function truth(c: C, path: Path): boolean | undefined {
  if (reuse) return reusing(seenOf(truthSeen, c), path, p => truthOf(c, p))
  let memo = truthMemo.get(path)
  if (!memo) truthMemo.set(path, (memo = new WeakMap()))
  if (memo.has(c)) return memo.get(c)
  const out = truthOf(c, path)
  memo.set(c, out)
  return out
}
function truthOf(c: C, path: Path): boolean | undefined {
  switch (c.op) {
    case 'flag': throw new Error('flags are inlined before the kernel sees them')
    case 'all': return undefined // closed before a goal is checked; opaque here, so it gives a leaf nothing
    case 'not': { const t = truth(c.x, path); return t === undefined ? undefined : !t }
    case 'and': case 'or': {
      const ts = c.xs.map(y => truth(y, path)), dominant = c.op === 'or'
      return ts.includes(dominant) ? dominant : ts.every(t => t === !dominant) ? !dominant : undefined
    }
    case '<': case '<=': case '=': {
      const cmp = comparison(c, path)
      if (!cmp) return undefined
      const ts = cmp.when.map(lin => decide(lin, path))
      return ts.includes(false) ? false : ts.every(t => t === true) ? true : undefined
    }
    default: return unreachable(c)
  }
}

// The linear facts a hypothesis gives under the path (each lin <= 0).
export function facts(c: C, path: Path, positive = true): Lin[] {
  switch (c.op) {
    case 'flag': throw new Error('flags are inlined before the kernel sees them')
    case 'all': return []
    case 'not': return facts(c.x, path, !positive)
    case 'and': case 'or': {
      if ((c.op === 'and') === positive) return c.xs.flatMap(y => facts(y, path, positive))
      const open = c.xs.filter(y => truth(y, path) !== !positive)
      return open.length === 0 ? [k(1)] : open.length === 1 ? facts(open[0]!, path, positive) : []
    }
    case '<': case '<=': case '=': {
      const cmp = comparison(c, path)
      if (!cmp) return []
      if (positive) return cmp.when
      const open = cmp.unless.filter(atoms => !atoms.some(lin => decide(lin, path) === false))
      return open.length === 0 ? [k(1)] : open.length === 1 ? open[0]! : []
    }
    default: return unreachable(c)
  }
}

// What a leaf's derivation must refute.
export function leafConstraints(goal: Goal, path: Path): Constraint[] { return leafRows(goal, path, h => facts(h, path)) }
// The same rows, for the prover's search: each hypothesis' facts as they were at an earlier path of the goal's where
// every decision they read was the same (facts read the path only through those decisions), and found afresh, with
// what they read recorded, otherwise. The kernel's check never uses it: it rebuilds every row as leafConstraints does.
const factsSeen = new WeakMap<Goal, Map<C, Seen<Lin[]>>>()
export function leafConstraintsReusing(goal: Goal, path: Path): Constraint[] {
  let byHyp = factsSeen.get(goal)
  if (!byHyp) factsSeen.set(goal, (byHyp = new Map()))
  return leafRows(goal, path, h => {
    let seen = byHyp.get(h)
    if (!seen) byHyp.set(h, (seen = {}))
    return reusing(seen, path, p => facts(h, p))
  })
}
// A value of the path that reads it only through decisions (facts, truth, linear forms, and what is built of them): as
// it was at an earlier path where each decision it read is the same, else found afresh, on a copy of the path (so no
// memo made without recording answers it), with what it read recorded in `seen`. `seen` is a trie of the decisions
// read, in the order they were read: a value's next decision depends only on the answers to those before it, so
// following the path's answers from the root reaches the value found for the same answers, if there is one.
type Decisions = [string, boolean | undefined][]
// A leaf holds a value and every decision it read; a branch sits where two values' decisions first part (at index
// `at`, the decision's key), so a value's run of decisions shared with no other costs no nodes.
type Node<T> = {at: number, key: string, next: Map<boolean | undefined, Node<T>>} | {reads: Decisions, out: T}
export type Seen<T> = {root?: Node<T>, size?: number}
// Past `reuseKeep` values a trie starts afresh: a long search would otherwise keep every value it ever found.
const reuseKeep = 16
function remember<T>(seen: Seen<T>, reads: Decisions, out: T): void {
  if ((seen.size = (seen.size ?? 0) + 1) > reuseKeep) { seen.root = undefined; seen.size = 1 }
  const leaf: Node<T> = {reads, out}
  let node = seen.root, parent: {next: Map<boolean | undefined, Node<T>>} | undefined, via: boolean | undefined
  while (node && 'key' in node) {
    // A value that read otherwise than the trie says (none does: the decisions are deterministic) is not kept.
    if (reads[node.at]?.[0] !== node.key) return
    parent = node; via = reads[node.at]![1]
    node = node.next.get(via)
  }
  const put = (n: Node<T>) => { if (parent) parent.next.set(via, n); else seen.root = n }
  if (!node) { put(leaf); return }
  const i = node.reads.findIndex((d, j) => reads[j]?.[0] !== d[0] || reads[j]![1] !== d[1])
  if (i < 0 || reads[i]?.[0] !== node.reads[i]![0]) return
  put({at: i, key: node.reads[i]![0], next: new Map([[node.reads[i]![1], node], [reads[i]![1], leaf]])})
}
export function reusing<T>(seen: Seen<T>, path: Path, f: (path: Path) => T): T {
  let node = seen.root
  while (node && 'key' in node) node = node.next.get(path.get(node.key)?.holds)
  if (node && node.reads.every(([key, holds]) => path.get(key)?.holds === holds)) {
    if (recording) for (const [key, holds] of node.reads) recording.set(key, holds)
    return node.out
  }
  const outer = recording, mode = reuse
  recording = new Map()
  reuse = true
  try {
    const out = f(new Map(path))
    remember(seen, [...recording], out)
    return out
  } finally {
    // What was read inside is read by the outer value too.
    if (outer) for (const [key, holds] of recording) outer.set(key, holds)
    recording = outer
    reuse = mode
  }
}
// While the prover reuses (inside `reusing`), a term's linear form, a comparison and a condition's truth are reused the
// same way, each by the decisions it reads: only what a new decision touches is read again. The kernel's check never
// runs in this mode: it reads every term afresh on every path.
let reuse = false
const linearSeen = new WeakMap<E, Seen<Lin | undefined>>(), comparisonSeen = new WeakMap<C, Seen<Comparison>>(), truthSeen = new WeakMap<C, Seen<boolean | undefined>>()
const seenOf = <K extends object, T>(m: WeakMap<K, Seen<T>>, k: K): Seen<T> => { let s = m.get(k); if (!s) m.set(k, (s = {})); return s }
function leafRows(goal: Goal, path: Path, factsOf: (h: C) => Lin[]): Constraint[] {
  const rows: Constraint[] = [...path.values()].map((a, i) => ({...atomOf(a.lin, a.holds), src: {atom: i}}))
  for (const [i, h] of goal.hyps.entries()) for (const lin of factsOf(h)) rows.push({lin, label: '', src: {fact: i}})
  const names = new Set(rows.flatMap(r => Object.keys(r.lin).filter(key => key !== '1')))
  // Two reads of one map whose keys the path proves equal are equal.
  const cells = [...names].filter(isCell).map(name => ({name, map: name.slice(0, name.indexOf('[')), key: keyOf(name)}))
  for (const [i, p] of cells.entries()) for (const q of cells.slice(i + 1)) {
    if (p.map !== q.map) continue
    const d = sub(p.key, q.key)
    if (decide(d, path) === true && decide(scale(d, -1), path) === true) rows.push({lin: sub(v(p.name), v(q.name)), label: '', src: {pair: [p.name, q.name]}}, {lin: sub(v(q.name), v(p.name)), label: '', src: {pair: [p.name, q.name]}})
  }
  // Each term column's rows, and the columns those rows bring in turn.
  const seen = new Set<string>(), todo = [...names].filter(n => n.startsWith('⟦'))
  while (todo.length) {
    const name = todo.pop()!
    if (seen.has(name)) continue
    seen.add(name)
    for (const lin of termRows(name, path)) {
      rows.push({lin, label: '', src: {term: name}})
      for (const key of Object.keys(lin)) if (key !== '1') { names.add(key); if (key.startsWith('⟦') && !seen.has(key)) todo.push(key) }
    }
  }
  for (const name of names) rows.push({lin: {[name]: -1}, label: '', src: {nat: name}})
  return rows
}
const keyOf = (cell: string): Lin => {
  const inner = cell.slice(cell.indexOf('[') + 1, -1)
  const out: Lin = {}
  // Keys are canonical texts `name:coef` joined by ',' at the outer level; a name may itself be a cell with brackets.
  let depth = 0, start = 0
  const parts: string[] = []
  for (let i = 0; i <= inner.length; i++) {
    const ch = inner[i]
    if (ch === '[') depth++
    else if (ch === ']') depth--
    else if ((ch === ',' && depth === 0) || i === inner.length) { if (i > start) parts.push(inner.slice(start, i)); start = i + 1 }
  }
  for (const part of parts) { const at = part.lastIndexOf(':'); out[part.slice(0, at)] = Number(part.slice(at + 1)) }
  return out
}

// A leaf may also use the product of two of its rows: p <= 0 and q <= 0 give p·q >= 0, as nlinarith does; and the
// square of any linear form t, which holds whatever t's sign: t·t >= 0 (a sum of squares, as a Positivstellensatz
// certificate has). The squares follow the leaf's rows, then the products; a pair may name a square or an earlier
// product (an index past the leaf's rows), each a row of the same kind, so degrees go higher.
export function withProducts(rows: Constraint[], pairs: [number, number][], squares: Lin[] = []): Constraint[] {
  const out = [...rows]
  for (const t of squares) { const tt = times(t, t); out.push(tt ? {lin: scale(tt, -1), label: ''} : {lin: {}, label: ''}) }
  for (const [i, j] of pairs) {
    const p = out[i], q = out[j], pq = p && q ? times(p.lin, q.lin) : undefined
    out.push(pq ? {lin: scale(pq, -1), label: ''} : {lin: {}, label: ''})
  }
  return out
}

export function check(goal: Goal, tree: Tree, path: Path = new Map()): boolean {
  if ('leaf' in tree) return checkRefutation(withProducts(leafConstraints(goal, path), tree.products ?? [], tree.squares), tree.leaf)
  const id = canon(tree.split)
  if (path.has(id) || Object.keys(tree.split).every(key => key === '1')) return false
  const yes = new Map(path).set(id, {lin: tree.split, holds: true}), no = new Map(path).set(id, {lin: tree.split, holds: false})
  return check(goal, tree.yes, yes) && check(goal, tree.no, no)
}

// --- machines ----------------------------------------------------------------------------------------------------------

// Every constant and factor is a natural, so every value a machine computes is one (∸ truncates).
function natural(e: E): boolean {
  switch (e.op) {
    case 'var': return true
    case 'const': return Number.isInteger(e.value) && e.value >= 0
    case 'mul': return Number.isInteger(e.k) && e.k >= 0 && natural(e.a)
    case 'prod': return natural(e.a) && natural(e.b)
    case 'if': return naturalC(e.c) && natural(e.then) && natural(e.else)
    case 'get': return natural(e.key)
    case 'add': case 'sub': case 'min': case 'max': return natural(e.a) && natural(e.b)
    default: return unreachable(e)
  }
}
const naturalC = (c: C): boolean => c.op === 'flag' ? true : c.op === 'all' ? naturalC(c.c) : c.op === 'not' ? naturalC(c.x) : c.op === 'and' || c.op === 'or' ? c.xs.every(naturalC) : natural(c.a) && natural(c.b)

// Substitution: variables by terms, and each map read by what the map holds (the start's constant, or a write over the
// map before the step).
export type Subst = {vars: Record<string, E>, maps: Record<string, (key: E) => E>, flags: Record<string, C>}
export function substE(e: E, s: Subst): E {
  switch (e.op) {
    case 'var': return s.vars[e.name] ?? e
    case 'const': return e
    case 'mul': return {...e, a: substE(e.a, s)}
    case 'prod': return {...e, a: substE(e.a, s), b: substE(e.b, s)}
    case 'if': return {op: 'if', c: substC(e.c, s), then: substE(e.then, s), else: substE(e.else, s)}
    case 'get': { const key = substE(e.key, s); return s.maps[e.map] ? s.maps[e.map]!(key) : {op: 'get', map: e.map, key} }
    case 'add': case 'sub': case 'min': case 'max': return {...e, a: substE(e.a, s), b: substE(e.b, s)}
    default: return unreachable(e)
  }
}
export function substC(c: C, s: Subst): C {
  if (c.op === 'flag') { const f = s.flags[c.name]; if (!f) throw new Error(`unknown flag ${c.name}`); return f }
  if (c.op === 'not') return {op: 'not', x: substC(c.x, s)}
  if (c.op === 'all') { const keys = boundOf(c), vars = Object.fromEntries(Object.entries(s.vars).filter(([n]) => !keys.includes(n))); return {...c, c: substC(c.c, {...s, vars})} }
  if (c.op === 'and' || c.op === 'or') return {op: c.op, xs: c.xs.map(y => substC(y, s))}
  return {...c, a: substE(c.a, s), b: substE(c.b, s)}
}
const mentions = (c: C, names: string[]): boolean => JSON.stringify(c).match(/"name":"([^"]+)"/g)?.some(m => names.includes(m.slice(8, -1))) ?? false
// A precondition reads the params and nothing else: no state, no request, no map.
const aboutParams = (c: C, params: string[]): boolean => !JSON.stringify(c).includes('"op":"get"') && (JSON.stringify(c).match(/"name":"([^"]+)"/g) ?? []).every(m => params.includes(m.slice(8, -1)))
const preOf = (o: {params: string[], pre?: C}): C[] => {
  if (o.pre && !(aboutParams(o.pre, o.params) && naturalC(o.pre))) throw new Error('a precondition reads only the params')
  return o.pre ? [o.pre] : []
}

// Instances: for each law that holds at every key, the keys (over the state before the step) the proof assumes it at;
// for a law about every two keys or more, the tuples, flattened (a tuple's keys in a row, `forall` first).
export type Instances = Record<string, E[]>

// --- runs: the one algebra under every obligation ----------------------------------------------------------------------

// Every obligation below is one inclusion: the runs a sequence of tests and steps allows, from a first frame (a copy of
// the state), are contained in a conclusion. A run is kept symbolically: the hypotheses met along it, each read at the
// frame it was met at, and the frame it ends at, every name a term over the first frame (and the inputs read on the
// way). Its goal is the hypotheses with the conclusion refuted. The induction rule, step laws, progress, loops, folds
// and k-step laws are each a few of these moves; nothing else turns a machine into goals.
type Run = {hyps: C[], at: Subst}
type Update = {vars: Record<string, E>, maps: Record<string, MapUpdate>}
const identity: Subst = {vars: {}, maps: {}, flags: {}}
const from = (at: Subst = identity): Run => ({hyps: [], at})
// Conditions that hold where the run is.
const holds = (r: Run, cs: C[]): Run => ({hyps: [...r.hyps, ...cs.map(c => substC(c, r.at))], at: r.at})
// Names read where the run is: inputs named for this step (a request's terms, or fresh names for a later step), and the
// maps a request carries, renamed for a later step.
const reading = (r: Run, vars: Record<string, E>, maps: Record<string, string> = {}): Run => ({hyps: r.hyps, at: {...r.at, vars: {...r.at.vars, ...vars},
  maps: {...r.at.maps, ...Object.fromEntries(Object.entries(maps).map(([map, name]) => [map, (key: E): E => ({op: 'get', map: name, key})]))}}})
// One step: each name the update sets is its term read where the run is; a map read after it is the written value at
// the written key, and what the map held before elsewhere (or, written at every key, its value at the key read).
const step = (r: Run, u: Update): Run => {
  const at = r.at, before = (map: string, key: E): E => (at.maps[map] ? at.maps[map]!(key) : {op: 'get', map, key})
  return {hyps: r.hyps, at: {
    vars: {...at.vars, ...Object.fromEntries(Object.entries(u.vars).map(([n, e]) => [n, substE(e, at)]))},
    maps: {...at.maps, ...Object.fromEntries(Object.entries(u.maps).map(([map, w]) => [map, 'each' in w
      ? (key: E): E => substE(w.value, {...at, vars: {...at.vars, [w.each]: key}})
      : (key: E): E => ({op: 'if', c: {op: '=', a: key, b: substE(w.key, at)}, then: substE(w.value, at), else: before(map, key)})]))},
    flags: at.flags,
  }}
}
// The state after a step, named: each state variable a fresh name n~j equal to its term there, which later frames read,
// so a run of k steps is k small frames rather than a term nesting each state in the next (which grows as 3^k when a
// step reads its state thrice). The names are new to the goal; each equation holds of the run that took the steps.
const nameState = (r: Run, state: string[], j: number): Run => ({
  hyps: [...r.hyps, ...state.map(n => ({op: '=', a: {op: 'var', name: stateName(n, j)}, b: r.at.vars[n] ?? {op: 'var', name: n}}) as C)],
  at: {...r.at, vars: {...r.at.vars, ...Object.fromEntries(state.map(n => [n, {op: 'var', name: stateName(n, j)} as E]))}},
})
export const stateName = (n: string, j: number) => `${n}~${j}`
// The conclusion read at the run's end: plain names at the last frame.
const atEnd = (r: Run, c: C): C => substC(c, r.at)
// The conclusion read across the run: plain names at the first frame, primed names (s', and M'[k] as a read of the map
// named M') at the last; the first step's inputs as it read them, and its flags, decided where it was taken.
const across = (r: Run, c: C, state: string[], maps: string[], first: {inputs: Record<string, E>, flags: Record<string, C>}): C => substC(c, {
  vars: {...first.inputs, ...Object.fromEntries(state.map(n => [`${n}'`, r.at.vars[n] ?? {op: 'var', name: n}]))},
  maps: Object.fromEntries(maps.map(map => [`${map}'`, (key: E): E => (r.at.maps[map] ? r.at.maps[map]!(key) : {op: 'get', map, key})])),
  flags: first.flags,
})
const goal = (name: string, r: Run, conclusion: C): Goal => ({name, hyps: [...r.hyps, {op: 'not', x: conclusion}]})
// A machine's flags as its terms read them (decided before the step, over the frame it starts from): a plain flag its
// condition (through the flags before it), a quantified flag (one whose condition holds at every key) its 0/1 variable
// ?f, which `closing` ties to the condition.
const flagsOf = (m: Machine): Record<string, C> => {
  const out: Record<string, C> = {}
  for (const [f, c] of Object.entries(m.step.flags ?? {})) out[f] = c.op === 'all' ? {op: '=', a: {op: 'var', name: `?${f}`}, b: {op: 'const', value: 1}} : substC(c, {vars: {}, maps: {}, flags: out})
  return out
}
const quantified = (m: Machine) => Object.entries(m.step.flags ?? {}).filter((e): e is [string, Extract<C, {op: 'all'}>] => e[1].op === 'all')
// The keys a quantifier binds: its key, and a quantified flag's further keys (a condition at every tuple of keys).
export const boundOf = (c: Extract<C, {op: 'all'}>): string[] => [c.key, ...(c.keys ?? [])]
// A quantified flag's witnesses, one per key: w?f, then w2?f, w3?f.
export const witnessesOf = (f: string, q: Extract<C, {op: 'all'}>): string[] => boundOf(q).map((_, i) => (i ? `w${i + 1}?${f}` : `w?${f}`))
// A comparison between two of a flag's keys, plainly (i < j, i ≤ j, i = j).
const crossing = (c: C, keys: string[]): boolean => (c.op === '<' || c.op === '<=' || c.op === '=') && c.a.op === 'var' && c.b.op === 'var' && c.a.name !== c.b.name && keys.includes(c.a.name) && keys.includes(c.b.name)
// A condition over several keys with each comparison between two of them set aside (as 0 ≤ 0): what reads each key on
// its own. (Kept per condition and keys: the runtimes ask at every step.)
const crossCache = new WeakMap<C, Map<string, C>>()
export const crossFree = (c: C, keys: string[]): C => {
  const id = keys.join(','), hit = crossCache.get(c)?.get(id)
  if (hit) return hit
  const zero: E = {op: 'const', value: 0}
  const e = (t: E): E => (t.op === 'if' ? {...t, c: crossFree(t.c, keys), then: e(t.then), else: e(t.else)} : t.op === 'get' ? {...t, key: e(t.key)} : t.op === 'mul' ? {...t, a: e(t.a)}
    : t.op === 'add' || t.op === 'sub' || t.op === 'min' || t.op === 'max' || t.op === 'prod' ? {...t, a: e(t.a), b: e(t.b)} : t)
  const out: C = crossing(c, keys) ? {op: '<=', a: zero, b: zero} : c.op === 'not' ? {op: 'not', x: crossFree(c.x, keys)} : c.op === 'and' || c.op === 'or' ? {op: c.op, xs: c.xs.map(y => crossFree(y, keys))}
    : c.op === 'all' ? {...c, c: crossFree(c.c, keys)} : c.op === 'flag' ? c : {...c, a: e(c.a), b: e(c.b)}
  if (!crossCache.has(c)) crossCache.set(c, new Map())
  crossCache.get(c)!.set(id, out)
  return out
}
// A machine's step as an update, its flags inlined.
const updateOf = (m: Machine): Update => {
  const flags: Subst = {vars: {}, maps: {}, flags: flagsOf(m)}
  return {
    vars: Object.fromEntries(Object.entries(m.step.state ?? {}).map(([n, e]) => [n, substE(e, flags)])),
    maps: Object.fromEntries(Object.entries(m.step.maps ?? {}).map(([map, w]) => [map, 'each' in w ? {each: w.each, value: substE(w.value, flags)} : {key: substE(w.key, flags), value: substE(w.value, flags)}])),
  }
}
const inlineFlags = (m: Machine, c: C): C => substC(c, {vars: {}, maps: {}, flags: flagsOf(m)})
// A quantified flag ?f, closed: it is 0 or 1; where it is 1, its condition holds at each key the proof names (instances
// under ?f); where it is 0, the condition fails at a fresh witness w?f. A real step decides ?f by the condition, and if
// that fails some key fails it, so these hold of every real step: a goal that refutes them refutes the machine.
// Over several keys, the instances are tuples (flattened, as Instances keeps them) and there is a witness per key.
const closing = (m: Machine, instances: Instances): C[] => quantified(m).flatMap(([f, q]): C[] => {
  const v: E = {op: 'var', name: `?${f}`}, zero: E = {op: 'const', value: 0}, one: E = {op: 'const', value: 1}, names = boundOf(q), n = names.length
  const body = (keys: E[]): C => substC(q.c, {vars: Object.fromEntries(names.map((key, i) => [key, keys[i]!])), maps: {}, flags: flagsOf(m)})
  const inst = instances[`?${f}`] ?? []
  return [{op: '<=', a: v, b: one}, ...Array.from({length: Math.floor(inst.length / n)}, (_, t): C => ({op: 'or', xs: [{op: '=', a: v, b: zero}, body(inst.slice(t * n, (t + 1) * n))]})),
    {op: 'or', xs: [{op: '=', a: v, b: one}, {op: 'not', x: body(witnessesOf(f, q).map((name): E => ({op: 'var', name})))}]}]
})
// The names a later step (j >= 2) reads its request by: inputs, quantified flags and their witnesses, and carried maps.
const laterNames = (m: Machine, j: number) => ({
  vars: Object.fromEntries([...m.inputs, ...quantified(m).flatMap(([f, q]) => [`?${f}`, ...witnessesOf(f, q)])].map(name => [name, {op: 'var', name: `${name}@${j}`} as E])),
  maps: Object.fromEntries((m.inputMaps ?? []).map(map => [map, `${map}@${j}`])),
})
// The laws assumed where the run is: each plain law, and each every-key law at the keys the proof names.
export const assumed = (laws: Law[], instances: Instances): C[] => laws.flatMap(l => {
  const keys = instances[l.name] ?? []
  if (l.keys?.length) {
    const names = [l.forall!, ...l.keys], n = names.length
    return Array.from({length: Math.floor(keys.length / n)}, (_, t) => substC(l.holds, {vars: Object.fromEntries(names.map((name, i) => [name, keys[t * n + i]!])), maps: {}, flags: {}}))
  }
  return l.forall ? keys.map(key => substC(l.holds, {vars: {[l.forall!]: key}, maps: {}, flags: {}})) : [l.holds]
})
// The facts about the functions, at the keys the proof names: as they are (they read the params and functions alone, so
// any frame reads them alike).
const given = (m: Machine, r: Run, instances: Instances): Run => ({hyps: [...r.hyps, ...assumed(m.facts ?? [], instances)], at: r.at})
// The start: the state's start values over the params, every map cell its constant.
const startOf = (m: Machine): Subst => ({vars: {...m.state}, maps: Object.fromEntries(Object.entries(m.maps ?? {}).map(([map, c]) => [map, () => ({op: 'const', value: c})])), flags: {}})

// --- scope -----------------------------------------------------------------------------------------------------------

// Every name a machine reads is one it declares. A goal reads an undeclared name as one more free natural, so a proof
// would still be sound about the machine as written; but the runtimes have no value for it, so the proof would be about
// a machine that never runs. Refused here, before any goal is made.
type Reads = {vars: Set<string>, maps: Set<string>, flags: Set<string>}
function reads(t: E | C, out: Reads = {vars: new Set(), maps: new Set(), flags: new Set()}): Reads {
  switch (t.op) {
    case 'var': out.vars.add(t.name); break
    case 'const': break
    case 'get': out.maps.add(t.map); reads(t.key, out); break
    case 'flag': out.flags.add(t.name); break
    case 'all': { const inner = reads(t.c); for (const key of boundOf(t)) inner.vars.delete(key); for (const k of ['vars', 'maps', 'flags'] as const) for (const name of inner[k]) out[k].add(name); break }
    case 'not': reads(t.x, out); break
    case 'and': case 'or': for (const y of t.xs) reads(y, out); break
    case 'mul': reads(t.a, out); break
    case 'if': reads(t.c, out); reads(t.then, out); reads(t.else, out); break
    case 'add': case 'sub': case 'min': case 'max': case 'prod': case '<': case '<=': case '=': reads(t.a, out); reads(t.b, out); break
    default: unreachable(t)
  }
  return out
}
function inScope(what: string, ts: (E | C)[], vars: string[], maps: string[] = [], flags: string[] = []) {
  for (const t of ts) {
    const r = reads(t)
    for (const name of r.vars) if (!vars.includes(name)) throw new Error(`${what} reads ${name}, which it doesn't declare`)
    for (const map of r.maps) if (!maps.includes(map)) throw new Error(`${what} reads the map ${map}, which it doesn't declare`)
    for (const flag of r.flags) if (!flags.includes(flag)) throw new Error(`${what} reads the flag ${flag}, which it doesn't declare`)
  }
}
// A name the kernel's linear forms would read as something else: '1' is the constant, and '*', '[', ']', ',' and ':'
// build monomials and cells. Such a name could never be proven about; refused instead, with its name.
const plainName = (what: string, name: string) => { if (name === '1' || /[*[\],:]/.test(name)) throw new Error(`${what}: the name ${name} is reserved (1, or * [ ] , :)`) }
const distinct = (what: string, names: string[]) => { const seen = new Set<string>(); for (const name of names) { if (seen.has(name)) throw new Error(`${what} declares ${name} twice`); seen.add(name) } }

// A machine (without its history: historyMachine checks that and scopes the plain machine it makes) and its laws. The
// step reads params, inputs and the state before it; a flag reads the flags declared before it; a start value reads the
// params; a law reads the params, the state, the maps and its own key.
export function scope(m: Machine, laws: Law[] = []) {
  const state = Object.keys(m.state), maps = Object.keys(m.maps ?? {}), flags = Object.keys(m.step.flags ?? {}), carried = m.inputMaps ?? [], fns = Object.keys(m.fns ?? {})
  const names = [...m.params, ...m.inputs, ...state]
  distinct(m.name, [...names, ...maps, ...carried, ...fns])
  for (const name of [...names, ...maps, ...carried, ...fns, ...flags]) plainName(m.name, name)
  for (const name of Object.keys(m.step.state ?? {})) if (!state.includes(name)) throw new Error(`${m.name}'s step sets ${name}, which isn't in its state`)
  for (const map of Object.keys(m.step.maps ?? {})) if (!maps.includes(map)) throw new Error(`${m.name}'s step writes the map ${map}, which it doesn't declare`)
  // The step reads the maps a request carries too. A key bound by a quantified flag or a write at every key is new and
  // read only as a map's key (so every key the maps hold nothing at reads alike); a quantifier is a whole flag, nowhere
  // else.
  const readable = [...maps, ...carried, ...fns]
  const bound = (what: string, key: string, t: E | C) => {
    plainName(what, key)
    if ([...names, ...readable, ...flags].includes(key)) throw new Error(`${what}: the key ${key} is already a name of ${m.name}`)
    keyOnly(what, t, key, fns)
  }
  inScope(`${m.name}'s start`, Object.values(m.state), m.params)
  flags.forEach((f, i) => {
    const c = m.step.flags![f]!, what = `${m.name}'s flag ${f}`
    // A quantified flag's body reads no flag (the twin decides quantified flags before the plain ones).
    if (c.op === 'all') {
      const keys = boundOf(c), body = crossFree(c.c, keys)
      distinct(what, keys)
      for (const key of keys) { bound(what, key, body); apart(what, body, key, keys) }
      unquantified(what, c.c); inScope(what, [c.c], [...names, ...keys], readable, [])
    }
    else { unquantified(what, c); inScope(what, [c], names, readable, flags.slice(0, i)) }
  })
  for (const [map, w] of Object.entries(m.step.maps ?? {})) {
    const what = `${m.name}'s write to ${map}`
    if ('each' in w) { bound(what, w.each, w.value); unquantified(what, w.value); inScope(what, [w.value], [...names, w.each], readable, flags) }
    else { unquantified(what, w.key); unquantified(what, w.value); inScope(what, [w.key, w.value], names, readable, flags) }
  }
  for (const e of Object.values(m.step.state ?? {})) unquantified(`${m.name}'s step`, e)
  inScope(`${m.name}'s step`, Object.values(m.step.state ?? {}), names, readable, flags)
  if (m.assume) { unquantified(`${m.name}'s assumption`, m.assume); inScope(`${m.name}'s assumption`, [m.assume], names, readable, flags) }
  if (m.pre) inScope(`${m.name}'s precondition`, [m.pre], m.params)
  const facts = m.facts ?? []
  distinct(`${m.name}'s laws and facts`, [...laws, ...facts].map(l => l.name))
  for (const law of [...laws, ...facts]) {
    const what = facts.includes(law) ? `fact ${law.name}` : `law ${law.name}`
    for (const key of [law.forall, ...(law.keys ?? [])]) if (key && [...names, ...maps, ...carried, ...fns].includes(key)) throw new Error(`${what}'s key ${key} is already a name of ${m.name}`)
    if (law.keys?.length && (!law.forall || new Set([law.forall, ...law.keys]).size !== law.keys.length + 1)) throw new Error(`${what}: further keys come with a first, each a different name`)
    if (law.name.startsWith('?')) throw new Error(`${what}: a name starting with ? is a flag's (its instances)`)
    unquantified(what, law.holds)
  }
  const keysOf = (l: Law) => [...(l.forall ? [l.forall] : []), ...(l.keys ?? [])]
  for (const law of laws) inScope(`law ${law.name}`, [law.holds], [...m.params, ...state, ...keysOf(law)], [...maps, ...fns])
  // A fact reads the params and the functions alone: what holds of them holds at every state.
  for (const fact of facts) inScope(`fact ${fact.name}`, [fact.holds], [...m.params, ...keysOf(fact)], fns)
}

// A key bound in t is read in key terms only: the key, or the key plus or less a term that doesn't read it (k + e, e + k,
// k ∸ e), each a map's key (no function's: a function's values don't stop where a map's cells do) or a side of a
// comparison whose other side doesn't read the key. Then t is constant between finitely many keys (the runtimes'
// breakpoints: each map's cells and each compared value, shifted by the offsets), so a runtime decides it on those.
const readsKey = (t: E | C, key: string) => JSON.stringify(t).includes(`"op":"var","name":${JSON.stringify(key)}`)
export const keyTerm = (e: E, key: string): boolean => e.op === 'var' ? e.name === key
  : e.op === 'add' ? (e.a.op === 'var' && e.a.name === key && !readsKey(e.b, key)) || (e.b.op === 'var' && e.b.name === key && !readsKey(e.a, key))
  : e.op === 'sub' && e.a.op === 'var' && e.a.name === key && !readsKey(e.b, key)
function keyOnly(what: string, t: E | C, key: string, fns: string[] = []): void {
  const bad = () => { throw new Error(`${what}: the key ${key} is read only in a map's key or a comparison, alone or plus or less a term that doesn't read it`) }
  const walk = (u: E | C): void => {
    switch (u.op) {
      case 'var': if (u.name === key) bad(); break
      case 'get': if (!(keyTerm(u.key, key) && !fns.includes(u.map))) walk(u.key); break
      case 'const': case 'flag': break
      case 'not': walk(u.x); break
      case 'all': walk(u.c); break
      case 'and': case 'or': u.xs.forEach(walk); break
      case 'mul': walk(u.a); break
      case 'if': walk(u.c); walk(u.then); walk(u.else); break
      case '<': case '<=': case '=':
        if (keyTerm(u.a, key) && !readsKey(u.b, key)) walk(u.b)
        else if (keyTerm(u.b, key) && !readsKey(u.a, key)) walk(u.a)
        else { walk(u.a); walk(u.b) }
        break
      case 'add': case 'sub': case 'min': case 'max': case 'prod': walk(u.a); walk(u.b); break
      default: unreachable(u)
    }
  }
  walk(t)
}
// Over several keys, each read apart from the others: no offset of its key terms, and no value it is compared with, reads
// another (the comparisons between two of them, plainly, are set aside before: crossFree).
function apart(what: string, t: C, key: string, keys: string[]): void {
  const others = keys.filter(k => k !== key), other = (e: E) => others.some(k => readsKey(e, k))
  const walk = (u: E | C): void => {
    if ((u.op === 'get' && keyTerm(u.key, key) && other(u.key))
      || ((u.op === '<' || u.op === '<=' || u.op === '=') && ((keyTerm(u.a, key) && (other(u.a) || other(u.b))) || (keyTerm(u.b, key) && (other(u.a) || other(u.b))))))
      throw new Error(`${what}: the keys ${keys.join(', ')} are each read on their own, and compared with one another only plainly (i < j, i <= j, i = j)`)
    for (const x of Object.values(u)) if (x && typeof x === 'object') (Array.isArray(x) ? x : [x]).forEach(y => walk(y as E | C))
  }
  walk(t)
}
// Whether the key is read only as a map's key, plainly (what the GPU searches decide: every cell, and one past them).
export const plainKey = (t: E | C, key: string): boolean => {
  const walk = (u: E | C): boolean => {
    switch (u.op) {
      case 'var': return u.name !== key
      case 'get': return (u.key.op === 'var' && u.key.name === key) || walk(u.key)
      case 'const': case 'flag': return true
      case 'not': return walk(u.x)
      case 'all': return walk(u.c)
      case 'and': case 'or': return u.xs.every(walk)
      case 'mul': return walk(u.a)
      case 'if': return walk(u.c) && walk(u.then) && walk(u.else)
      case 'add': case 'sub': case 'min': case 'max': case 'prod': case '<': case '<=': case '=': return walk(u.a) && walk(u.b)
      default: return unreachable(u)
    }
  }
  return walk(t)
}
// No quantifier inside t: a quantifier is a whole flag.
function unquantified(what: string, t: E | C): void {
  if (JSON.stringify(t).includes('"op":"all"')) throw new Error(`${what}: a condition at every key is a flag of its own (flags: {name: all(...)})`)
}

// --- histories ---------------------------------------------------------------------------------------------------------

// A term or condition that reads only these names, and no map.
const readsOnly = (t: E | C, names: string[]): boolean => !JSON.stringify(t).includes('"op":"get"') && !JSON.stringify(t).includes('"op":"flag"') && (JSON.stringify(t).match(/"name":"([^"]+)"/g) ?? []).every(m => names.includes(m.slice(8, -1)))
const homogeneous = (e: E, names: string[]): boolean => e.op === 'var' ? names.includes(e.name) : e.op === 'add' ? homogeneous(e.a, names) && homogeneous(e.b, names) : e.op === 'mul' ? Number.isInteger(e.k) && e.k >= 0 && homogeneous(e.a, names) : false

// A machine with a history as a plain one: each sum a state variable from 0, plus its term at the request whenever the
// step keeps the request; each query an input; each relation part of the step's assumption. Sound because, at every
// step, a sum is the sum of its term over the history so far and a query the sum of its term over the same records:
// a relation that holds record by record (the goals returned, one per relation, over a record's fields as free
// naturals) holds of the sums, since a and b are linear without a constant and `when` doesn't read the record.
export function historyMachine(m: Machine): {machine: Machine, goals: Goal[]} {
  const h = m.history
  if (!h) return {machine: m, goals: []}
  const queries = Object.keys(h.queries), sums = Object.keys(h.sums), plainInputs = m.inputs.filter(i => !queries.includes(i))
  const fields = h.record.map(f => `r.${f}`)
  const taken = [...m.params, ...m.inputs, ...Object.keys(m.state), ...Object.keys(m.step.state ?? {})]
  // r.<field> names a record's field and nothing else: a param, input or state variable of that name would be read as
  // the field in the per-record goal and as itself in `pre` and `when`.
  const ok = [...taken, ...sums].every(name => !name.startsWith('r.'))
    && queries.every(q => m.inputs.includes(q)) && h.record.every(f => plainInputs.includes(f)) && sums.every(s => !taken.includes(s))
    && Object.values(h.sums).every(g => natural(g) && readsOnly(g, [...fields, ...m.params]))
    && Object.values(h.queries).every(g => natural(g) && readsOnly(g, [...fields, ...m.params, ...plainInputs])) && naturalC(h.keep)
    && (h.relations ?? []).every(r => naturalC(r.when) && readsOnly(r.when, [...m.params, ...plainInputs]) && r.holds.op === '<=' && homogeneous(r.holds.a, [...sums, ...queries]) && homogeneous(r.holds.b, [...sums, ...queries]))
  if (!ok) throw new Error('a history: sums read the record and params, queries also the request\'s other inputs, relations are homogeneous a <= b under a condition on the params and the request')
  inScope(`${m.name}'s keep`, [h.keep], [...m.params, ...m.inputs, ...Object.keys(m.state), ...sums], Object.keys(m.maps ?? {}), Object.keys(m.step.flags ?? {}))
  if (h.prune && !(h.record.includes(h.prune.order) && natural(h.prune.after) && readsOnly(h.prune.after, m.params))) throw new Error('a history is pruned by a recorded input and a term over the params')
  const atRequest: Subst = {vars: Object.fromEntries(h.record.map(f => [`r.${f}`, {op: 'var', name: f} as E])), maps: {}, flags: {}}
  // The relations conjoined to the assumption as the Lean twin builds them (History.lean's HMachine.plain: assume ∧
  // r₁ ∧ … ∧ true), so the two read the same assumption.
  const TRUE: C = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  const relations = (h.relations ?? []).map(r => ({op: 'or', xs: [{op: 'not', x: r.when}, r.holds]}) as C).reduceRight<C>((acc, r) => ({op: 'and', xs: [r, acc]}), TRUE)
  const machine: Machine = {
    ...m, history: undefined,
    state: {...m.state, ...Object.fromEntries(sums.map(s => [s, {op: 'const', value: 0} as E]))},
    step: {...m.step, state: {...m.step.state, ...Object.fromEntries(sums.map(s => [s, {op: 'add', a: {op: 'var', name: s}, b: {op: 'if', c: h.keep, then: substE(h.sums[s]!, atRequest), else: {op: 'const', value: 0}}} as E]))}},
    assume: {op: 'and', xs: [m.assume ?? TRUE, relations]},
  }
  const perRecord: Subst = {vars: {...h.sums, ...h.queries}, maps: {}, flags: {}}
  const goals = (h.relations ?? []).map((r, i) => ({name: `relation ${i + 1} @record`, hyps: [...preOf(m), r.when, {op: 'not', x: substC(r.holds, perRecord)} as C]}))
  // Pruning: a record whose order plus `after` is at most the request's adds nothing to any query. With requests in
  // nondecreasing order (the runtimes refuse one that goes back), such a record adds nothing to any later query either,
  // so dropping it changes no query: these goals are about the runtimes, the laws are proven over the whole history.
  if (h.prune) {
    const {order, after} = h.prune
    const gone: C = {op: '<=', a: {op: 'add', a: {op: 'var', name: `r.${order}`}, b: after}, b: {op: 'var', name: order}}
    for (const [q, g] of Object.entries(h.queries)) goals.push({name: `prune @query ${q}`, hyps: [...preOf(m), gone, {op: 'not', x: {op: '<=', a: g, b: {op: 'const', value: 0}}}]})
  }
  return {machine, goals}
}

// `only`: the goals of that law alone (the prover's instance search asks for one law's at a time).
export function obligations(m: Machine, laws: Law[], instances: Record<string, Instances> = {}, only?: number): Goal[] {
  if (m.history) { const {machine, goals} = historyMachine(m); return [...obligations(machine, laws, instances, only), ...(only === undefined ? goals : [])] }
  scope(m, laws)
  const ok = [...Object.values(m.state), ...Object.values(m.step.state ?? {}), ...Object.values(m.step.maps ?? {}).flatMap(w => ('each' in w ? [w.value] : [w.key, w.value]))].every(natural)
    && Object.values(m.step.flags ?? {}).every(naturalC) && laws.every(l => naturalC(l.holds)) && Object.values(m.maps ?? {}).every(c => Number.isInteger(c) && c >= 0)
  if (!ok || !(m.facts ?? []).every(l => naturalC(l.holds)) || laws.some(l => mentions(l.holds, m.inputs))) throw new Error('a negative constant or factor, or a law about a request, is outside the kernel')
  // A law that holds at every key is proven at a fresh one.
  // A law about every two keys keeps its second key as it is: a fresh name nothing else reads, so the goal is about every
  // value of it too (the Lean twin reads it so).
  const proven = (law: Law) => (law.forall ? substC(law.holds, {vars: {[law.forall]: {op: 'var', name: `${law.forall}#`}}, maps: {}, flags: {}}) : law.holds)
  const pre = preOf(m), u = updateOf(m), assume = m.assume ? [inlineFlags(m, m.assume)] : []
  return laws.flatMap((law, i) => {
    if (only !== undefined && i !== only) return []
    // At the start: the precondition, and no request. One step: from a state where the laws hold, a request allowed.
    // The facts hold throughout, read where the run begins (they read no state).
    const start = given(m, holds(from(startOf(m)), pre), instances[law.name] ?? {})
    const turn = step(holds(given(m, from(), instances[law.name] ?? {}), [...pre, ...assume, ...assumed(laws, instances[law.name] ?? {}), ...closing(m, instances[law.name] ?? {})]), u)
    return [goal(`${law.name} @start`, start, atEnd(start, proven(law))), goal(`${law.name} @step`, turn, atEnd(turn, proven(law)))]
  })
}

// The whole set at once: every goal has a tree, and every tree checks.
export function checkLaws(m: Machine, laws: Law[], proof: {instances: Record<string, Instances>, trees: Record<string, Tree>}): boolean {
  return obligations(m, laws, proof.instances).every(g => proof.trees[g.name] !== undefined && check(g, proof.trees[g.name]!))
}

// --- loops: termination ------------------------------------------------------------------------------------------------

// A loop runs `body` while `while` holds; each turn may read fresh inputs (a server's delay, a page's size). It halts if a
// natural-valued rank, over the state and params, drops on every turn the invariants allow: naturals can't drop forever.
export type Loop = {name: string, params: string[], inputs: string[], state: Record<string, E>, while: C, body: Record<string, E>, pre?: C, assume?: C}

// A loop is a machine: its state, a turn's inputs as a request, its body taken where `while` holds and the state kept
// where it fails. Its invariants are the machine's laws, and that it halts is a liveness: from anywhere, `while` fails
// later, every request helpful, the rank the loop's (Live.lean's Loop.machine and loop_halts_of: then no run of turns is
// infinite). `while` and the rank read the state and params, not the turn's input.
// A rank may be a tuple, compared in order (lexicographically): the first part drops, or it stays and the rest drops.
// Tuples of naturals can't drop forever either; nested loops need them (an outer count, then an inner one).
// A rank reads the state and params only: one that reads the turn's input drops against this turn's input, but the next
// turn measures it with a fresh one, so nothing need decrease (while x < w, x := x + 1, rank w ∸ x, w = x + 1 each turn).
export const loopMachine = (l: Loop): Machine => ({
  name: l.name, params: l.params, inputs: l.inputs, state: l.state,
  step: {state: Object.fromEntries(Object.entries(l.body).map(([v, e]) => [v, {op: 'if', c: l.while, then: e, else: {op: 'var', name: v}} as E]))},
  ...(l.pre ? {pre: l.pre} : {}), ...(l.assume ? {assume: l.assume} : {}),
})
export const loopLiveness = (l: Loop, rank: E | E[]): Liveness => ({name: `${l.name} halts`, from: trueC, to: {op: 'not', x: l.while}, rank, request: {}})
export function loopObligations(l: Loop, laws: Law[], rank: E | E[]): Goal[] {
  const ranks = Array.isArray(rank) ? rank : [rank]
  const parts = [...Object.values(l.state), ...Object.values(l.body), ...ranks]
  const names = [...l.params, ...l.inputs, ...Object.keys(l.state)]
  distinct(l.name, names)
  for (const name of Object.keys(l.body)) if (!(name in l.state)) throw new Error(`${l.name}'s body sets ${name}, which isn't in its state`)
  inScope(`${l.name}'s start`, Object.values(l.state), l.params)
  inScope(l.name, [...Object.values(l.body), ...(l.assume ? [l.assume] : [])], names)
  inScope(`${l.name}'s while`, [l.while], [...l.params, ...Object.keys(l.state)])
  inScope(`${l.name}'s precondition`, l.pre ? [l.pre] : [], l.params)
  inScope(`${l.name}'s rank and laws`, [...ranks, ...laws.map(law => law.holds)], [...l.params, ...Object.keys(l.state)])
  if (ranks.some(r => mentions({op: '=', a: r, b: r}, l.inputs))) throw new Error('a rank reads the state and params, not the turn\'s input')
  if (!parts.every(natural) || !naturalC(l.while) || !laws.every(law => !law.forall && !law.keys?.length && naturalC(law.holds) && !mentions(law.holds, l.inputs))) throw new Error('outside the kernel')
  const m = loopMachine(l), {stay, cover, helps} = livenessParts(m, loopLiveness(l, rank))
  return [...obligations(m, laws, {}), ...[stay, cover, ...helps].map(sl => stepLawObligations(m, laws, {}, sl)[0]!)]
}

// --- loops: a run that never ends ----------------------------------------------------------------------------------------

// The claim (Lean: NonTerm.lean's `NeverEnds`): for some params meeting the precondition, a run of turns from the start
// goes on forever. The certificate is a closed recurrent set with its successor given (`never_ends_of`): `set`, a
// condition over the state and params; `wit`, a term per input over the state and params, the turn taken from a state of
// the set; `start`, the params' values (every other name 0); `stem`, each turn's inputs (an input not named is 0) from the
// start into the set. The start and the stem are evaluated exactly, as Lean's naturals (bigint, ∸ truncating); the
// closure goal is a kernel goal: a state of the set whose witnessed turn fails `while` or the assumption, or ends outside
// the set. Refuted, the witnessed turn from the set's states, again and again, is a run that never ends. A loop's
// halting (loopObligations) and this claim contradict each other (`halts_not_never_ends`).
export type Recur = {start: Record<string, number>, stem: Record<string, number>[], set: C, wit: Record<string, E>, tree: Tree}
// The closure goal, built as Lean's recurGoal builds it: [set, ¬(while ∧ (assume ∧ set after the body)), each read at the
// witnessed request].
export function recurGoal(l: Loop, r: Pick<Recur, 'set' | 'wit'>): Goal {
  const w: Subst = {vars: r.wit, maps: {}, flags: {}}
  return {name: `${l.name} never ends: the set is closed`, hyps: [r.set, {op: 'not', x: {op: 'and', xs: [substC(l.while, w), substC(l.assume ?? trueC, w),
    substC(substC(r.set, {vars: l.body, maps: {}, flags: {}}), w)]}}]}
}
// Lean's evalE and evalC over naturals with every map cell 0 (NonTerm.lean's noMaps): exact, never rounded.
const natE = (e: E, env: Record<string, bigint>): bigint => {
  switch (e.op) {
    case 'var': return env[e.name] ?? 0n
    case 'const': return BigInt(e.value)
    case 'add': return natE(e.a, env) + natE(e.b, env)
    case 'sub': { const d = natE(e.a, env) - natE(e.b, env); return d > 0n ? d : 0n }
    case 'mul': return BigInt(e.k) * natE(e.a, env)
    case 'prod': return natE(e.a, env) * natE(e.b, env)
    case 'min': { const a = natE(e.a, env), b = natE(e.b, env); return a < b ? a : b }
    case 'max': { const a = natE(e.a, env), b = natE(e.b, env); return a > b ? a : b }
    case 'if': return natC(e.c, env) ? natE(e.then, env) : natE(e.else, env)
    case 'get': return 0n
    default: return unreachable(e)
  }
}
const natC = (c: C, env: Record<string, bigint>): boolean => {
  switch (c.op) {
    case '<=': return natE(c.a, env) <= natE(c.b, env)
    case '<': return natE(c.a, env) < natE(c.b, env)
    case '=': return natE(c.a, env) === natE(c.b, env)
    case 'and': return c.xs.every(x => natC(x, env))
    case 'or': return c.xs.some(x => natC(x, env))
    case 'not': return !natC(c.x, env)
    case 'flag': case 'all': throw new Error('a loop reads no flag')
    default: return unreachable(c)
  }
}
// Lean's checkRecur: the witness sets only inputs; the start meets the precondition; the stem's turns meet `while` and
// the assumption, and the state after them is in the set; the closure goal's tree checks. A certificate outside the
// language (names the loop doesn't declare, values that aren't naturals, a set reading a turn's input) is refused.
export function checkRecur(l: Loop, r: Recur): boolean {
  const names = [...l.params, ...l.inputs, ...Object.keys(l.state)], values = (o: Record<string, number>) => Object.values(o).every(x => Number.isSafeInteger(x) && x >= 0)
  distinct(l.name, names)
  for (const name of Object.keys(l.body)) if (!(name in l.state)) throw new Error(`${l.name}'s body sets ${name}, which isn't in its state`)
  inScope(`${l.name}'s start`, Object.values(l.state), l.params)
  inScope(l.name, [...Object.values(l.body), ...(l.assume ? [l.assume] : [])], names)
  inScope(`${l.name}'s while`, [l.while], [...l.params, ...Object.keys(l.state)])
  inScope(`${l.name}'s precondition`, l.pre ? [l.pre] : [], l.params)
  inScope(`${l.name}'s recurrent set and witness`, [r.set, ...Object.values(r.wit)], [...l.params, ...Object.keys(l.state)])
  if (![...Object.values(l.state), ...Object.values(l.body), ...Object.values(r.wit)].every(natural) || ![l.while, r.set, ...(l.pre ? [l.pre] : []), ...(l.assume ? [l.assume] : [])].every(naturalC)) throw new Error('outside the kernel')
  if (!Object.keys(r.start).every(n => l.params.includes(n)) || !values(r.start) || !r.stem.every(t => Object.keys(t).every(n => l.inputs.includes(n)) && values(t))) throw new Error(`${l.name}: a start names params and a stem's turn inputs, each a natural`)
  if (!Object.keys(r.wit).every(n => l.inputs.includes(n))) return false
  let env: Record<string, bigint> = Object.fromEntries(names.map(n => [n, BigInt(r.start[n] ?? 0)]))
  if (!natC(l.pre ?? trueC, env)) return false
  const apply = (body: Record<string, E>, at: Record<string, bigint>) => ({...at, ...Object.fromEntries(Object.entries(body).map(([n, e]) => [n, natE(e, at)]))})
  env = apply(l.state, env)
  for (const turn of r.stem) {
    const at = {...env, ...Object.fromEntries(l.inputs.map(n => [n, BigInt(turn[n] ?? 0)]))}
    if (!natC(l.while, at) || !natC(l.assume ?? trueC, at)) return false
    env = apply(l.body, at)
  }
  return natC(r.set, env) && check(recurGoal(l, r), r.tree)
}

// --- progress: laws with "there is a request" ----------------------------------------------------------------------

// "In every reachable state where `when` holds, some request makes `then` true of the step": proven by naming the
// request (a term per input over the state and params) and proving it allowed (the machine's assumption holds of it)
// and that the step it causes makes `then` hold. `then` reads the state before the step by plain names and after it by
// primed names (s', and M'[k] as a read of the map named M'). The laws assumed must be proven inductive on their own.
export function progressObligations(m: Machine, laws: Law[], instances: Instances, p: {name: string, when: C, then: C, request: Record<string, E>}): Goal[] {
  if (!m.inputs.every(i => i in p.request) || !Object.values(p.request).every(natural) || mentions(p.when, m.inputs)) throw new Error('outside the kernel')
  for (const e of Object.values(p.request)) if (mentions({op: '=', a: e, b: e}, m.inputs)) throw new Error('a request is named from the state and params')
  const req: Subst = {vars: p.request, maps: {}, flags: {}}
  const flags = Object.fromEntries(Object.entries(flagsOf(m)).map(([f, c]) => [f, substC(c, req)]))
  // The run: a state where the laws and `when` hold, the named request (its quantified flags closed), then the step it
  // causes. Maps a request carries are left as any maps: the step is shown for all of them.
  const before = holds(given(m, from(), instances), [...preOf(m), ...assumed(laws, instances), p.when])
  const asked = holds(reading(before, p.request), closing(m, instances))
  const caused = step(asked, updateOf(m))
  return [
    ...(m.assume ? [goal(`${p.name}: the request is allowed`, asked, substC(inlineFlags(m, m.assume), req))] : []),
    goal(`${p.name}: the step it causes`, caused, across(caused, p.then, Object.keys(m.state), Object.keys(m.maps ?? {}), {inputs: p.request, flags})),
  ]
}

// --- liveness: "from leads to to", under fairness ----------------------------------------------------------------------

// "Whenever `from` holds, `to` holds later", in every run that takes each helpful request infinitely often. The rank is
// naturals over the state and params compared in order (one term, or several: the first that differs decides). A
// helpful request names some inputs by terms over the state and params (the others, and the maps it carries, stay
// free: any value helps) and the region where it helps (everywhere, if none). Every goal is a step law, while `from`
// holds and `to` doesn't: each request allowed keeps `from` or reaches `to`, and reaches `to`, lowers the rank, or keeps
// it with every region it is in kept (stay); some region holds (cover); and each helpful request taken in its region
// reaches `to` or lowers the rank (helps). Then along such a run the rank can't drop forever; once it stops, the region
// it is in stays and its request comes (the Lean twin's `leads_sound`, `sleads_sound`). The conditions are built
// exactly as Live.lean builds them, two parts per and/or.
export type Helpful = {when?: C, request: Record<string, E>}
export type Liveness = {name: string, from: C, to: C, rank: E | E[], request?: Record<string, E>, helpful?: Helpful[]}
const zero: E = {op: 'const', value: 0}
export const trueC: C = {op: '<=', a: zero, b: zero}, falseC: C = {op: '<', a: zero, b: zero}
const and2 = (a: C, b: C): C => ({op: 'and', xs: [a, b]}), or2 = (a: C, b: C): C => ({op: 'or', xs: [a, b]})
const lexLt = (after: E[], before: E[]): C => (after.length && before.length ? or2({op: '<', a: after[0]!, b: before[0]!}, and2({op: '=', a: after[0]!, b: before[0]!}, lexLt(after.slice(1), before.slice(1)))) : falseC)
const eqs = (after: E[], before: E[]): C => (after.length && before.length ? and2({op: '=', a: after[0]!, b: before[0]!}, eqs(after.slice(1), before.slice(1))) : trueC)
const keep = (ws: C[], prime: (c: C) => C): C => (ws.length ? and2(or2({op: 'not', x: ws[0]!}, prime(ws[0]!)), keep(ws.slice(1), prime)) : trueC)
const anyOf = (ws: C[]): C => (ws.length ? or2(ws[0]!, anyOf(ws.slice(1))) : falseC)
const named = (req: [string, E][]): C => (req.length ? and2({op: '=', a: {op: 'var', name: req[0]![0]}, b: req[0]![1]}, named(req.slice(1))) : trueC)
export const livenessRanks = (l: Liveness): E[] => (Array.isArray(l.rank) ? l.rank : [l.rank])
export const livenessHelpful = (l: Liveness): {when: C, request: Record<string, E>}[] => {
  if ((l.request === undefined) === (l.helpful === undefined)) throw new Error(`liveness ${l.name}: a helpful request, or helpful requests with their regions`)
  return (l.helpful ?? [{request: l.request!}]).map(h => ({when: h.when ?? trueC, request: h.request}))
}
export function livenessParts(m: Machine, l: Liveness): {stay: StepLaw, cover: StepLaw, helps: StepLaw[]} {
  // A machine with a history as its plain machine (its sums are state, its queries inputs no request names).
  const plain = m.history ? historyMachine(m).machine : m
  const queries = Object.keys(m.history?.queries ?? {}), client = plain.inputs.filter(i => !queries.includes(i))
  const ranks = livenessRanks(l), helpful = livenessHelpful(l)
  if (!ranks.length || !helpful.length) throw new Error(`liveness ${l.name}: a rank of one natural or more, and a helpful request or more`)
  for (const [what, t] of [['from', l.from], ['to', l.to], ...ranks.map((r, i) => [`rank ${i + 1}`, {op: '=', a: r, b: r}] as const), ...helpful.map((h, i) => [`region ${i + 1}`, h.when] as const)] as const) {
    if (mentions(t as C, plain.inputs)) throw new Error(`liveness ${l.name}: ${what} reads the state and params, not a request`)
  }
  for (const h of helpful) for (const [input, t] of Object.entries(h.request)) {
    if (!client.includes(input)) throw new Error(`liveness ${l.name}: a helpful request names inputs a client sends (${input} is ${queries.includes(input) ? 'a query, computed from the log' : 'none'})`)
    if (mentions({op: '=', a: t, b: t}, plain.inputs)) throw new Error(`liveness ${l.name}: the request's ${input} is a term over the state and params`)
  }
  const after: Subst = {vars: Object.fromEntries(Object.keys(plain.state).map(n => [n, {op: 'var', name: `${n}'`} as E])), maps: Object.fromEntries(Object.keys(plain.maps ?? {}).map(map => [map, (key: E): E => ({op: 'get', map: `${map}'`, key})])), flags: {}}
  const prime = (c: C) => substC(c, after), ranks2 = ranks.map(r => substE(r, after)), to2 = prime(l.to)
  const pending = and2(l.from, {op: 'not', x: l.to}), lower = lexLt(ranks2, ranks), regions = helpful.map(h => h.when)
  return {
    stay: {name: `${l.name}: each step stays or gets there, the rank kept only with its region`, when: pending,
      then: and2(or2(prime(l.from), to2), or2(to2, or2(lower, and2(eqs(ranks2, ranks), keep(regions, prime)))))},
    cover: {name: `${l.name}: some helpful request applies`, when: pending, then: anyOf(regions)},
    helps: helpful.map((h, i) => ({name: `${l.name}: helpful request ${i + 1}`, when: and2(pending, and2(h.when, named(Object.entries(h.request)))), then: or2(to2, lower)})),
  }
}

// --- step laws: what one step does ------------------------------------------------------------------------------------

// "In every reachable state, every request the machine allows takes a step where `then` holds": `then` reads the state,
// maps, params and the request as they are before the step by plain names, and the state and maps after it by primed
// names (s', and M'[k] as a read of the map named M'); flags (decided before the step) may be read too. `when` narrows
// the requests the law is about; `forall` names a key the law holds at every value of (a free variable of the goal). One
// goal per law: the precondition, the laws (proven inductive on their own, assumed at
// the keys the proof names), the request's assumption and `when` as hypotheses, `then` refuted with the primed names read
// through the step. A machine with a history is its plain machine (sums are state, queries are inputs).
//
// With `steps: k`, the law is about k steps in a row: `then` reads the state before the first by plain names and after
// the last by primed ones, the first request by plain names and the j-th (j >= 2) as input@j; `when` is one condition
// for the first step, or one per step, each read at the state that step starts from with its request by plain names.
// The laws hold at every state on the way (each is reachable), so each is assumed before each step.
export type StepLaw = {name: string, when?: C | C[], then: C, forall?: string, keys?: string[], steps?: number}
export function stepLawObligations(machine: Machine, laws: Law[], instances: Instances, sl: StepLaw): Goal[] {
  const m = machine.history ? historyMachine(machine).machine : machine
  scope(m, laws)
  const k = sl.steps ?? 1
  // Past 64 the cost is the bound (proving grows about as k³: 64 steps in about 5 s on Modal; Lean checks 32 in about 14 s, 64 in about 47 s).
  if (!Number.isInteger(k) || k < 1 || k > 64) throw new Error(`step law ${sl.name}: steps is a whole number from 1 to 64`)
  const whens = sl.when === undefined ? [] : Array.isArray(sl.when) ? sl.when : [sl.when]
  if (whens.length > k) throw new Error(`step law ${sl.name}: one when per step at most`)
  const state = Object.keys(m.state), maps = Object.keys(m.maps ?? {}), carried = m.inputMaps ?? [], flagNames = Object.keys(m.step.flags ?? {})
  const primes = [...state, ...maps].map(n => `${n}'`)
  const laters = Array.from({length: k - 1}, (_, i) => laterNames(m, i + 2))
  const later = laters.flatMap(l => Object.values(l.vars).map(e => (e as {name: string}).name)), laterMaps = laters.flatMap(l => Object.values(l.maps))
  const names = Array.from({length: k - 1}, (_, i) => state.map(n => stateName(n, i + 1))).flat()
  const taken = [...m.params, ...m.inputs, ...state, ...maps, ...carried]
  for (const p of [...primes, ...later, ...laterMaps, ...names]) if (taken.includes(p)) throw new Error(`${m.name}: ${p} is a name of the machine and a name a step law reads`)
  for (const key of [sl.forall, ...(sl.keys ?? [])]) if (key && [...taken, ...primes, ...later].includes(key)) throw new Error(`step law ${sl.name}'s key ${key} is already a name of ${m.name}`)
  if (sl.keys?.length && (!sl.forall || new Set([sl.forall, ...sl.keys]).size !== sl.keys.length + 1)) throw new Error(`step law ${sl.name}: further keys come with a first, each a different name`)
  unquantified(`step law ${sl.name}`, sl.then)
  inScope(`step law ${sl.name}`, [sl.then], [...taken, ...state.map(n => `${n}'`), ...later, ...(sl.forall ? [sl.forall] : []), ...(sl.keys ?? [])], [...maps, ...carried, ...maps.map(n => `${n}'`), ...laterMaps], flagNames)
  for (const w of whens) { unquantified(`step law ${sl.name}'s when`, w); inScope(`step law ${sl.name}'s when`, [w], taken, [...maps, ...carried], flagNames) }
  if (!naturalC(sl.then) || !whens.every(naturalC)) throw new Error(`step law ${sl.name}: a negative constant or factor is outside the kernel`)
  const u = updateOf(m), assume = m.assume ? [inlineFlags(m, m.assume)] : []
  let run = given(m, holds(from(), preOf(m)), instances)
  for (let j = 1; j <= k; j++) {
    if (j > 1) run = reading(run, laters[j - 2]!.vars, laters[j - 2]!.maps)
    run = step(holds(run, [...assumed(laws, instances), ...assume, ...(whens[j - 1] ? [inlineFlags(m, whens[j - 1]!)] : []), ...closing(m, instances)]), u)
    if (j < k) run = nameState(run, state, j)
  }
  return [goal(k === 1 ? `${sl.name} @step law` : `${sl.name} @${k} steps`, run, across(run, sl.then, state, maps, {inputs: {}, flags: flagsOf(m)}))]
}

// The laws' proof and every step law's tree: all must check.
// `perStep`: a step law's own instances, where it has them (else `instances`).
// Each frame's hypotheses read no name a later step's request is read by: the condition the Lean twin's proof needs
// (Sets.lean's checkSKStep, `avoids (szone s sl)`; plain flags are inlined here, so their names never occur), checked
// here alike. A quantified flag's keys are free of it: where the flag is 1 its condition holds at every key, so at a
// key a later step names too (and the flag, its witness and its condition read none).
const lawsOnly = (inst: Instances): Instances => Object.fromEntries(Object.entries(inst).filter(([n]) => !n.startsWith('?')))
export function checkStepLaws(m: Machine, laws: Law[], stepLaws: StepLaw[], proof: {laws: {instances: Record<string, Instances>, trees: Record<string, Tree>}, instances: Instances, perStep?: Record<string, Instances>, trees: Record<string, Tree>}): boolean {
  return checkLaws(m, laws, proof.laws) && stepLaws.every(sl => {
    const inst = proof.perStep?.[sl.name] ?? proof.instances, plain = m.history ? historyMachine(m).machine : m
    const zone = stepZone(plain, sl.steps ?? 1)
    return [...assumed(laws, inst), ...assumed(plain.facts ?? [], inst), ...closing(plain, lawsOnly(inst))].every(c => !mentions(c, zone))
      && stepLawObligations(m, laws, inst, sl).every(g => proof.trees[g.name] !== undefined && check(g, proof.trees[g.name]!))
  })
}
// The names a k-step law's run introduces past its first frame: each later step's inputs, quantified flags and their
// witnesses, and the state after each step but the last (stateName).
export const stepZone = (m: Machine, k: number): string[] => [
  ...Array.from({length: k - 1}, (_, i) => Object.values(laterNames(m, i + 2).vars).map(e => (e as {name: string}).name)).flat(),
  ...Array.from({length: k - 1}, (_, i) => Object.keys(m.state).map(n => stateName(n, i + 1))).flat(),
]

// --- k-induction: a law k steps in a row keep -------------------------------------------------------------------------

// A plain law (no key) holds in every reachable state if it holds at the start, after every run of j steps from the
// start for 1 ≤ j < k (the base), and after any k steps in a row from a reachable state, each step starting where it
// holds (the step). Every goal but the start's (the law's own @start goal) is a k-step law's, its `when`s and `then`
// built here from the law alone: the base of depth j reads its first state as the start (each state variable its start
// term) with the law there, and the law before each later step; the step reads the law before each of its k steps; `then`
// is the law with primed names. The Lean twin (KInd.lean's checkKInd) builds the same goals, and `kind_sound` proves
// that a checked certificate makes the law hold in every reachable state. The proof is a step laws' proof (the laws
// assumed, proven inductive as ever; each goal's tree by name), its start goal's instances `perStep[<law> @start]`.
export type KInduction = {law: Law, k: number}
export function kInductionSteps(machine: Machine, kl: KInduction): StepLaw[] {
  const m = machine.history ? historyMachine(machine).machine : machine, L = kl.law, k = kl.k
  if (L.forall || L.keys?.length || L.some?.length || L.ex) throw new Error(`k-induction of ${L.name}: a law with no key`)
  if (!Number.isInteger(k) || k < 1 || k > 64) throw new Error(`k-induction of ${L.name}: k is a whole number from 1 to 64`)
  // (as the twin's checkKInd: the law reads no request's name, flag or witness; the start reads none, nor a state
  // variable, nor a map; scope below asks the rest)
  const ext = [...m.inputs, ...quantified(m).flatMap(([f, q]) => [`?${f}`, ...witnessesOf(f, q)]), ...Object.keys(m.step.flags ?? {}).map(f => `?${f}`)]
  if (mentions(L.holds, ext) || Object.keys(m.state).some(n => ext.includes(n))) throw new Error(`k-induction of ${L.name}: reads a request's name or a flag`)
  for (const e of Object.values(m.state)) if (mentions({op: '=', a: e, b: e}, [...ext, ...Object.keys(m.state)]) || JSON.stringify(e).includes('"op":"get"')) throw new Error(`k-induction of ${L.name}: a start reads the params alone`)
  const start: C = {op: 'and', xs: Object.entries(m.state).map(([n, e]): C => ({op: '=', a: {op: 'var', name: n}, b: e}))}
  const after: Subst = {vars: Object.fromEntries(Object.keys(m.state).map(n => [n, {op: 'var', name: `${n}'`} as E])), maps: Object.fromEntries(Object.keys(m.maps ?? {}).map(map => [map, (key: E): E => ({op: 'get', map: `${map}'`, key})])), flags: {}}
  const then = substC(L.holds, after)
  return [
    ...Array.from({length: k - 1}, (_, i): StepLaw => ({name: `${L.name} @base ${i + 1}`, when: [{op: 'and', xs: [start, L.holds]}, ...Array.from({length: i}, () => L.holds)], then, steps: i + 1})),
    {name: `${L.name} @k-step`, when: Array.from({length: k}, () => L.holds), then, steps: k},
  ]
}
export const kInductionStart = (machine: Machine, kl: KInduction, instances: Instances): Goal => {
  const m = machine.history ? historyMachine(machine).machine : machine
  return obligations(m, [kl.law], {[kl.law.name]: instances})[0]!
}
export function checkKInduction(m: Machine, laws: Law[], kl: KInduction, proof: {laws: {instances: Record<string, Instances>, trees: Record<string, Tree>}, instances: Instances, perStep?: Record<string, Instances>, trees: Record<string, Tree>}): boolean {
  const steps = kInductionSteps(m, kl), plain = m.history ? historyMachine(m).machine : m
  scope(plain, [...laws, kl.law])
  const start = kInductionStart(m, kl, proof.perStep?.[`${kl.law.name} @start`] ?? proof.instances)
  return proof.trees[start.name] !== undefined && check(start, proof.trees[start.name]!) && checkStepLaws(m, laws, steps, proof)
}

// --- trees: structural induction ---------------------------------------------------------------------------------------

// A fold over binary trees whose leaves and nodes carry inputs: a leaf's state from its inputs, a node's from its
// children's (l_name, r_name) and its own inputs. A law holds of every tree if it holds at every leaf, and at a node
// whenever it holds at both children.
export type Fold = {name: string, params: string[], inputs: string[], leaf: Record<string, E>, node: Record<string, E>, pre?: C, assume?: C}

export function foldObligations(f: Fold, laws: Law[]): Goal[] {
  if (![...Object.values(f.leaf), ...Object.values(f.node)].every(natural) || !laws.every(law => !law.forall && !law.keys?.length && naturalC(law.holds) && !mentions(law.holds, f.inputs))) throw new Error('outside the kernel')
  const names = Object.keys(f.leaf)
  distinct(f.name, [...f.params, ...f.inputs, ...names])
  if (Object.keys(f.node).sort().join() !== [...names].sort().join()) throw new Error(`${f.name}'s leaf and node set the same names`)
  inScope(`${f.name}'s leaf`, [...Object.values(f.leaf), ...(f.assume ? [f.assume] : [])], [...f.params, ...f.inputs])
  inScope(`${f.name}'s node`, Object.values(f.node), [...f.params, ...f.inputs, ...names.flatMap(n => [`l_${n}`, `r_${n}`])])
  inScope(`${f.name}'s precondition`, f.pre ? [f.pre] : [], f.params)
  inScope(`${f.name}'s laws`, laws.map(law => law.holds), [...f.params, ...names])
  const side = (p: string): Subst => ({vars: Object.fromEntries(names.map(n => [n, {op: 'var', name: `${p}${n}`} as E])), maps: {}, flags: {}})
  // A fold's inputs are each leaf's and node's own, so its assumption holds at every leaf and node it reads them at.
  // A leaf is a start from its inputs; a node, a step from the frame of its two children, the laws holding at each.
  const assume = [...preOf(f), ...(f.assume ? [f.assume] : [])]
  const leaf = holds(from({vars: {...f.leaf}, maps: {}, flags: {}}), assume)
  const node = step(holds(from(), [...assume, ...laws.flatMap(h => [substC(h.holds, side('l_')), substC(h.holds, side('r_'))])]), {vars: f.node, maps: {}})
  return laws.flatMap(law => [goal(`${law.name} @leaf`, leaf, atEnd(leaf, law.holds)), goal(`${law.name} @node`, node, atEnd(node, law.holds))])
}

// --- rationals: Rationals.lean's twin --------------------------------------------------------------------------------
// A goal over the rationals: hypotheses over terms whose values are rationals (variables, rational constants, +, −
// not truncated, × by a rational constant, min, max, if; ≤, <, =, and, or, not), with no naturality row and no term
// column. A term's linear form is a row with integer coefficients over a positive denominator, computed exactly
// (bigint), as Lean's `linear`; a split's no side is the strict row −lin < 0; a leaf's derivation is checked by
// check.ts with no cut (Rationals.lean's checkQ). Each function below is the Lean definition of the same name in
// namespace Q; the exporter writes each leaf's inputs as the rows Lean finds among its own (`claimOk`).
export type Rat = {num: bigint, den: bigint}
export type QE =
  | {op: 'var', name: string}
  | {op: 'const', q: Rat}
  | {op: 'add' | 'sub' | 'min' | 'max', a: QE, b: QE}
  | {op: 'mul', k: Rat, a: QE}
  | {op: 'if', c: QC, then: QE, else: QE}
export type QC = {op: '<=' | '<' | '=', a: QE, b: QE} | {op: 'and' | 'or', a: QC, b: QC} | {op: 'not', x: QC}
export type QGoal = {name: string, hyps: QC[]}
// A row: coefficients by variable (none zero) and a constant; a form is a row over a positive denominator.
export type QRow = {cs: Map<string, bigint>, c: bigint}
export type LF = {row: QRow, den: bigint}
const bgcd = (a: bigint, b: bigint): bigint => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a }
// Lean's q.num and q.den: the reduced fraction (a denominator <= 0 is no rational).
export const ratNorm = (q: Rat): Rat => {
  if (q.den <= 0n) throw new Error('a rational has a positive denominator')
  const g = bgcd(q.num, q.den) || 1n
  return {num: q.num / g, den: q.den / g}
}
const rscale = (m: bigint, r: QRow): QRow => ({cs: new Map(m === 0n ? [] : [...r.cs].map(([x, c]) => [x, m * c])), c: m * r.c})
const radd = (a: QRow, b: QRow): QRow => {
  const cs = new Map(a.cs)
  for (const [x, c] of b.cs) { const s = (cs.get(x) ?? 0n) + c; if (s === 0n) cs.delete(x); else cs.set(x, s) }
  return {cs, c: a.c + b.c}
}
export const qdif = (a: LF, b: LF): QRow => radd(rscale(b.den, a.row), rscale(-a.den, b.row))
// A row as a Lin, its coefficients safe integers (else undefined: a row past 2^53 is not read, so the check is weaker,
// never wrong); and its key, as `canon` writes a Lin (zero coefficients dropped: Lean's `same` compares by value).
export const qLin = (r: QRow): Lin | undefined => {
  const out: Lin = {}
  for (const [x, c] of r.cs) { if (c < -(2n ** 53n) + 1n || c > 2n ** 53n - 1n) return undefined; out[x] = Number(c) }
  if (r.c !== 0n) { if (r.c < -(2n ** 53n) + 1n || r.c > 2n ** 53n - 1n) return undefined; out['1'] = Number(r.c) }
  return out
}
const linRow = (lin: Lin): QRow | undefined => {
  if (!Object.values(lin).every(c => Number.isSafeInteger(c))) return undefined
  const cs = new Map<string, bigint>()
  for (const [x, c] of Object.entries(lin)) if (x !== '1' && c !== 0) cs.set(x, BigInt(c))
  return {cs, c: BigInt(lin['1'] ?? 0)}
}
const rowKey = (r: QRow): string | undefined => { const lin = qLin(r); return lin && canon(lin) }
export function qdec(path: Path, r: QRow): boolean | undefined {
  if (r.cs.size === 0) return r.c <= 0n
  const key = rowKey(r)
  return key === undefined ? undefined : path.get(key)?.holds
}
export function qlinear(e: QE, path: Path): LF | undefined {
  switch (e.op) {
    case 'var': return e.name === '1' ? undefined : {row: {cs: new Map([[e.name, 1n]]), c: 0n}, den: 1n}
    case 'const': { const q = ratNorm(e.q); return {row: {cs: new Map(), c: q.num}, den: q.den} }
    case 'add': case 'sub': {
      const a = qlinear(e.a, path), b = qlinear(e.b, path)
      if (!a || !b) return undefined
      return {row: e.op === 'add' ? radd(rscale(b.den, a.row), rscale(a.den, b.row)) : qdif(a, b), den: a.den * b.den}
    }
    case 'mul': { const k = ratNorm(e.k), a = qlinear(e.a, path); return a && {row: rscale(k.num, a.row), den: k.den * a.den} }
    case 'min': case 'max': {
      const a = qlinear(e.a, path), b = qlinear(e.b, path)
      if (!a || !b) return undefined
      const d = qdec(path, qdif(a, b))
      return d === undefined ? undefined : (d === (e.op === 'min')) ? a : b
    }
    case 'if': { const t = qtruth(e.c, path); return t === undefined ? undefined : qlinear(t ? e.then : e.else, path) }
    default: return unreachable(e)
  }
}
export function qtruth(c: QC, path: Path): boolean | undefined {
  switch (c.op) {
    case '<=': case '<': case '=': {
      const a = qlinear(c.a, path), b = qlinear(c.b, path)
      if (!a || !b) return undefined
      if (c.op === '<=') return qdec(path, qdif(a, b))
      if (c.op === '<') { const d = qdec(path, qdif(b, a)); return d === undefined ? undefined : !d }
      const d1 = qdec(path, qdif(a, b)), d2 = qdec(path, qdif(b, a))
      return d1 === false || d2 === false ? false : d1 === true && d2 === true ? true : undefined
    }
    case 'and': case 'or': {
      const ta = qtruth(c.a, path), tb = qtruth(c.b, path), dominant = c.op === 'or'
      return ta === dominant || tb === dominant ? dominant : ta === !dominant && tb === !dominant ? !dominant : undefined
    }
    case 'not': { const t = qtruth(c.x, path); return t === undefined ? undefined : !t }
    default: return unreachable(c)
  }
}
// The rows (each with its strictness) a hypothesis gives under the path when it has the truth value `pos`.
export function qfacts(c: QC, path: Path, pos = true): [QRow, boolean][] {
  switch (c.op) {
    case 'not': return qfacts(c.x, path, !pos)
    case 'and': case 'or': {
      // and when true, or when false: both parts; otherwise the part the other one's truth leaves.
      if ((c.op === 'and') === pos) return [...qfacts(c.a, path, pos), ...qfacts(c.b, path, pos)]
      if (qtruth(c.a, path) === !pos) return qfacts(c.b, path, pos)
      if (qtruth(c.b, path) === !pos) return qfacts(c.a, path, pos)
      return []
    }
    case '<=': case '<': case '=': {
      const a = qlinear(c.a, path), b = qlinear(c.b, path)
      if (!a || !b) return []
      if (c.op === '<=') return pos ? [[qdif(a, b), false]] : [[qdif(b, a), true]]
      if (c.op === '<') return pos ? [[qdif(a, b), true]] : [[qdif(b, a), false]]
      if (pos) return [[qdif(a, b), false], [qdif(b, a), false]]
      if (qdec(path, qdif(a, b)) === true) return [[qdif(a, b), true]]
      if (qdec(path, qdif(b, a)) === true) return [[qdif(b, a), true]]
      return []
    }
    default: return unreachable(c)
  }
}
// A leaf's rows: the path's atoms (l <= 0, or −l < 0), then each hypothesis' facts; a row past 2^53 is left out.
export function qLeafRows(goal: QGoal, path: Path): Constraint[] {
  const rows: [QRow, boolean][] = [...[...path.values()].map(a => (a.holds ? [linRow(a.lin)!, false] : [rscale(-1n, linRow(a.lin)!), true]) as [QRow, boolean]),
    ...goal.hyps.flatMap(h => qfacts(h, path))]
  return rows.flatMap(([r, strict]) => { const lin = qLin(r); return lin ? [{lin, label: '', strict}] : [] })
}
// A split on a row the path decides already (or a constant one) is refused, as Lean's checkT refuses it.
export function checkQTree(goal: QGoal, tree: Tree, path: Path = new Map()): boolean {
  if ('leaf' in tree) return !tree.products?.length && !tree.squares?.length && checkRefutation(qLeafRows(goal, path), tree.leaf, false)
  const row = linRow(tree.split), lin = row && qLin(row)
  if (!row || !lin || qdec(path, row) !== undefined) return false
  const key = canon(lin)
  return checkQTree(goal, tree.yes, new Map(path).set(key, {lin, holds: true})) && checkQTree(goal, tree.no, new Map(path).set(key, {lin, holds: false}))
}

// Step machines over the rationals (Rationals.lean's Machine): params, inputs and state are rationals; `state` is each
// state variable's start over the params, `step` its value after a request (a variable it leaves out keeps its value).
export type QMachine = {name: string, params: string[], inputs: string[], state: Record<string, QE>, step: Record<string, QE>, pre?: QC, assume?: QC}
export type QLaw = {name: string, holds: QC}
export const qTrue: QC = {op: '<=', a: {op: 'const', q: {num: 0n, den: 1n}}, b: {op: 'const', q: {num: 0n, den: 1n}}}
export function qSubstE(e: QE, s: Record<string, QE>): QE {
  switch (e.op) {
    case 'var': return Object.hasOwn(s, e.name) ? s[e.name]! : e
    case 'const': return e
    case 'mul': return {...e, a: qSubstE(e.a, s)}
    case 'if': return {op: 'if', c: qSubstC(e.c, s), then: qSubstE(e.then, s), else: qSubstE(e.else, s)}
    case 'add': case 'sub': case 'min': case 'max': return {...e, a: qSubstE(e.a, s), b: qSubstE(e.b, s)}
    default: return unreachable(e)
  }
}
export function qSubstC(c: QC, s: Record<string, QE>): QC {
  switch (c.op) {
    case 'not': return {op: 'not', x: qSubstC(c.x, s)}
    case 'and': case 'or': return {op: c.op, a: qSubstC(c.a, s), b: qSubstC(c.b, s)}
    case '<=': case '<': case '=': return {op: c.op, a: qSubstE(c.a, s), b: qSubstE(c.b, s)}
    default: return unreachable(c)
  }
}
export function qOccurs(t: QE | QC, names: string[]): boolean {
  switch (t.op) {
    case 'var': return names.includes(t.name)
    case 'const': return false
    case 'mul': return qOccurs(t.a, names)
    case 'not': return qOccurs(t.x, names)
    case 'if': return qOccurs(t.c, names) || qOccurs(t.then, names) || qOccurs(t.else, names)
    case 'and': case 'or': return qOccurs(t.a, names) || qOccurs(t.b, names)
    case 'add': case 'sub': case 'min': case 'max': case '<=': case '<': case '=': return qOccurs(t.a, names) || qOccurs(t.b, names)
    default: return unreachable(t)
  }
}
// startGoal and stepGoal: the law refuted at the start, and after a step from where every law and the request's
// assumption hold.
export function qObligations(m: QMachine, laws: QLaw[], law: QLaw): {start: QGoal, step: QGoal} {
  const pre = m.pre ?? qTrue, assume = m.assume ?? qTrue
  return {
    start: {name: `${law.name} @start`, hyps: [pre, {op: 'not', x: qSubstC(law.holds, m.state)}]},
    step: {name: `${law.name} @step`, hyps: [pre, assume, ...laws.map(l => l.holds), {op: 'not', x: qSubstC(law.holds, m.step)}]},
  }
}
// checkMachine: the precondition reads no input and no state variable, no law reads an input, and each law's start
// and step goals are refuted by its trees.
export function checkQMachine(m: QMachine, laws: QLaw[], trees: Record<string, {start: Tree, step: Tree}>): boolean {
  const assigned = [...m.inputs, ...Object.keys(m.state), ...Object.keys(m.step)]
  if (m.pre && qOccurs(m.pre, assigned)) return false
  return laws.every(law => {
    const t = trees[law.name], goals = qObligations(m, laws, law)
    return !!t && !qOccurs(law.holds, m.inputs) && checkQTree(goals.start, t.start) && checkQTree(goals.step, t.step)
  })
}
