// Untrusted, like prove.ts: the tree search for goals over the rationals (kernel.ts's QGoal). A node reads its rows
// as the kernel does (qLeafRows); the incremental simplex (simplex.ts, over the rationals) picks a conflict's rows, the
// elimination (solver.ts, no cut) refutes them exactly, and that derivation is the leaf. A node it can't refute is
// split on an open atom: a choice a term leaves open (min, max, if), or a comparison a hypothesis needs decided before
// it gives rows (a disjunction, ≠). With no atom open, every hypothesis' rows say all it says under the path, so the
// elimination decides the node: refuted, or a model, exact (a counterexample to the goal, checked by evaluation).
// Linear arithmetic over ℚ is decidable and this search is complete for it: every split is on a finite set of atoms,
// and each leaf is decided.
import {type Constraint, type Lin, type Step, solve, work} from '../core/solver.ts'
import type {Rat} from '../core/q.ts'
import {type LF, type Path, type QC, type QE, type QGoal, type Tree, canon, qdec, qdif, qLeafRows, qLin, qlinear, qtruth} from './kernel.ts'
import {Simplex} from './simplex.ts'

export type QOutcome = {tree: Tree, nodes: number} | {stuck: 'sat' | 'unknown', witness?: Record<string, number>, rational?: Record<string, Rat>, path: Path, why?: string}

// The open atoms of a term: its undecided choices (and those inside), and an if's condition's while it is open.
function openE(e: QE, path: Path, out: Lin[]): void {
  switch (e.op) {
    case 'var': case 'const': return
    case 'mul': return openE(e.a, path, out)
    case 'add': case 'sub': openE(e.a, path, out); openE(e.b, path, out); return
    case 'min': case 'max': {
      openE(e.a, path, out); openE(e.b, path, out)
      const a = qlinear(e.a, path), b = qlinear(e.b, path)
      if (a && b) push(qdif(a, b), path, out)
      return
    }
    case 'if': {
      const t = qtruth(e.c, path)
      if (t === undefined) openC(e.c, path, out); else openE(t ? e.then : e.else, path, out)
      return
    }
  }
}
const push = (row: Parameters<typeof qLin>[0], path: Path, out: Lin[]) => { if (qdec(path, row) === undefined) { const lin = qLin(row); if (lin) out.push(lin) } }
const forms = (c: Extract<QC, {a: QE}>, path: Path): [LF, LF] | undefined => { const a = qlinear(c.a, path), b = qlinear(c.b, path); return a && b ? [a, b] : undefined }
// The atoms that decide a condition's truth.
function openC(c: QC, path: Path, out: Lin[]): void {
  switch (c.op) {
    case 'not': return openC(c.x, path, out)
    case 'and': case 'or': openC(c.a, path, out); openC(c.b, path, out); return
    case '<=': case '<': case '=': {
      openE(c.a, path, out); openE(c.b, path, out)
      const f = forms(c, path)
      if (!f) return
      if (c.op !== '<') push(qdif(f[0], f[1]), path, out)
      if (c.op !== '<=') push(qdif(f[1], f[0]), path, out)
    }
  }
}
// The atoms a hypothesis needs decided before its rows (kernel.ts's qfacts) say all it says: none for a comparison
// whose terms are decided, both parts of a conjunction, and for a disjunction the atoms that decide its parts.
function openH(c: QC, path: Path, out: Lin[], pos = true): void {
  switch (c.op) {
    case 'not': return openH(c.x, path, out, !pos)
    case 'and': case 'or': {
      if ((c.op === 'and') === pos) { openH(c.a, path, out, pos); openH(c.b, path, out, pos); return }
      if (qtruth(c.a, path) === !pos) return openH(c.b, path, out, pos)
      if (qtruth(c.b, path) === !pos) return openH(c.a, path, out, pos)
      openC(c.a, path, out); openC(c.b, path, out)
      return
    }
    case '<=': case '<': case '=': {
      const f = forms(c, path)
      if (!f) { openE(c.a, path, out); openE(c.b, path, out); return }
      if (c.op === '=' && !pos && qdec(path, qdif(f[0], f[1])) !== true && qdec(path, qdif(f[1], f[0])) !== true) push(qdif(f[0], f[1]), path, out)
    }
  }
}
export function openQ(goal: QGoal, path: Path): Lin[] {
  const out: Lin[] = [], last = goal.hyps.length - 1
  if (last >= 0) openH(goal.hyps[last]!, path, out)
  for (let i = 0; i < last; i++) openH(goal.hyps[i]!, path, out)
  const seen = new Set<string>()
  return out.filter(lin => { const key = canon(lin); return !seen.has(key) && (seen.add(key), true) })
}

// A derivation of the rows, by the simplex's conflict (its rows refuted exactly) or else the elimination over all.
function refute(rows: Constraint[], sx: Simplex, whole: boolean): {steps?: Step[], verdict?: ReturnType<typeof solve>} {
  let lp = sx.load(rows)
  if (lp.kind === 'sat') lp = sx.check()
  if (lp.kind === 'conflict') {
    const support = lp.rows.sort((x, y) => x - y), out = solve(support.map(i => rows[i]!), 20_000, false)
    if (out.kind === 'refuted') return {steps: out.steps.map(s => (s.kind === 'input' ? {...s, index: support[s.index]!} : s))}
  }
  if (!whole && lp.kind === 'sat') return {}
  const verdict = solve(rows, 20_000, false)
  return verdict.kind === 'refuted' ? {steps: verdict.steps} : {verdict}
}

export function growQ(goal: QGoal, opts: {until?: number, maxNodes?: number} = {}): QOutcome {
  const until = opts.until ?? performance.now() + 20_000, maxNodes = opts.maxNodes ?? 100_000
  let nodes = 0
  const sx = new Simplex(false)
  const go = (path: Path): QOutcome => {
    if (++nodes > maxNodes || performance.now() > until) return {stuck: 'unknown', path, why: nodes > maxNodes ? 'nodes' : 'time'}
    const rows = qLeafRows(goal, path)
    work.n += 1 + rows.length
    const open = openQ(goal, path)
    const r = refute(rows, sx, open.length === 0)
    if (r.steps) return {tree: {leaf: r.steps}, nodes}
    if (!open.length) {
      const v = r.verdict
      return v?.kind === 'sat' ? {stuck: 'sat', witness: v.witness, ...(v.rational ? {rational: v.rational} : {}), path} : {stuck: 'unknown', path, why: 'no split'}
    }
    const lin = open[0]!, key = canon(lin)
    const yes = go(new Map(path).set(key, {lin, holds: true}))
    if (!('tree' in yes)) return yes
    const no = go(new Map(path).set(key, {lin, holds: false}))
    if (!('tree' in no)) return no
    return {tree: {split: lin, yes: yes.tree, no: no.tree}, nodes}
  }
  return go(new Map())
}
