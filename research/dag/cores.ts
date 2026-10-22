// A refuted case's core: the decisions of its path that the rows its derivation reads depend on. A row of a hypothesis
// depends on the decisions its facts read (kernel.ts's `reusing` records them: a fresh trie's one leaf holds what was
// read), a term column's rows on what termRows read, an atom's row on that atom, two equal cells on their keys' atoms,
// a natural's row on nothing. Then the derivation is replayed at the core alone (each row it reads found again by its
// linear form among leafConstraints at the shorter path, as kernel/prove.ts's lift does): `steps` is the same
// derivation over the core's rows, or undefined when a row isn't there (the core was too small; the caller keeps the
// whole path). Untrusted: a DAG leaf is checked by check-dag.ts against the rows at its own path.
import type {Constraint, Lin, Step} from '../../core/solver.ts'
import {scale} from '../../core/solver.ts'
import {checkRefutation} from '../../core/check.ts'
import {type Goal, type Path, type Seen, canon, canonFlip, facts, leafConstraints, reusing, termRows, withProducts} from '../../kernel/kernel.ts'

export type Lit = string // `${canon key}=${holds}`
export const lit = (key: string, holds: boolean): Lit => `${key}=${holds ? 1 : 0}`

const readsOf = <T>(path: Path, f: (p: Path) => T): [string, boolean | undefined][] => {
  const seen: Seen<T> = {}
  reusing(seen, path, f)
  const root = seen.root as {reads?: [string, boolean | undefined][]} | undefined
  return root?.reads ?? []
}

// The rows a derivation reads, directly or through the products it multiplies.
export function usedRows(n: number, steps: Step[], products: [number, number][] = [], squares: Lin[] = []): Set<number> {
  const out = new Set<number>(), sq = squares.length
  const mark = (i: number): void => { if (i < n) out.add(i); else if (i >= n + sq) { const pq = products[i - n - sq]; if (pq) { mark(pq[0]); mark(pq[1]) } } }
  for (const st of steps) if (st.kind === 'input') mark(st.index)
  return out
}

export function coreOf(goal: Goal, path: Path, rows: Constraint[], used: Set<number>): Set<string> {
  const keys = [...path.keys()], core = new Set<string>()
  const add = (reads: [string, boolean | undefined][]) => { for (const [key, holds] of reads) if (holds !== undefined && path.has(key)) core.add(key) }
  const byFact = new Map<number, [string, boolean | undefined][]>(), byTerm = new Map<string, [string, boolean | undefined][]>()
  for (const i of used) {
    const s = rows[i]!.src
    if (!s || 'nat' in s) continue
    if ('atom' in s) core.add(keys[s.atom]!)
    else if ('fact' in s) { let r = byFact.get(s.fact); if (!r) byFact.set(s.fact, (r = readsOf(path, p => facts(goal.hyps[s.fact]!, p)))); add(r) }
    else if ('term' in s) { let r = byTerm.get(s.term); if (!r) byTerm.set(s.term, (r = readsOf(path, p => termRows(s.term, p)))); add(r) }
    else for (const [key, a] of path) { if (Object.keys(a.lin).some(n => s.pair.some(c => c.includes(n)))) core.add(key) }
  }
  return core
}

export const sub = (path: Path, keep: Set<string>): Path => new Map([...path].filter(([key]) => keep.has(key)))

// The derivation over the rows at `to` (a sub-path), or undefined if a row it reads isn't among them.
export function replay(goal: Goal, from: Constraint[], to: Path, steps: Step[], products?: [number, number][], squares?: Lin[]): {rows: Constraint[], steps: Step[], products?: [number, number][]} | undefined {
  const rows = leafConstraints(goal, to), at = new Map<string, number>()
  rows.forEach((r, i) => { const key = canon(r.lin); if (!at.has(key)) at.set(key, i) })
  const n = from.length, sq = squares?.length ?? 0
  const map = (i: number): number | undefined => (i < n ? at.get(canon(from[i]!.lin)) : i - n + rows.length)
  const out: Step[] = []
  for (const st of steps) {
    if (st.kind !== 'input') { out.push(st); continue }
    const j = map(st.index)
    if (j === undefined) return undefined
    out.push({...st, index: j})
  }
  const prods: [number, number][] = []
  for (const [i, j] of products ?? []) { const a = map(i), b = map(j); if (a === undefined || b === undefined) return undefined; prods.push([a, b]) }
  void sq
  if (!checkRefutation(withProducts(rows, prods, squares), out)) return undefined
  return {rows, steps: out, ...(products?.length ? {products: prods} : {})}
}

// The literal of a decision as a clause literal: the same atom decided either way by its canonical text, so the
// atom lin <= 0 and its flip 1 - lin <= 0 are one variable (the smaller text), with the sign the decision gives it.
export function normLit(key: string, lin: Lin, holds: boolean): {v: string, pos: boolean} {
  const flip = canonFlip(lin)
  return key <= flip ? {v: key, pos: holds} : {v: flip, pos: !holds}
}
export const negLin = (lin: Lin): Lin => scale(lin, -1)
