// Research twin of Count.lean's FrameCuts (MLDR-DESIGN.md Section 15.7). Not imported by kernel/kernel.ts: the
// production twin lands only when 15.5's ledger says frames still dominate, through the Lean-first route. Every
// function mirrors a Lean definition of the same name; FRAME-CUTS.md has the contract table.
import type {C, E} from '../../core/machine.ts'
import {type Lin, k} from '../../core/solver.ts'
import {type Count, type Goal, type LemmaCut, type Path, type Tree, canon, canonFlip, check, lemmaPath, truth} from '../../kernel/kernel.ts'

export type FrameCut = {when: Lin[], post: string, pre: string}

// Lean's dec: a constant row decides itself; otherwise the path's atom or its flip.
export function decide(lin: Lin, path: Path): boolean | undefined {
  if (Object.keys(lin).every(key => key === '1' || lin[key] === 0)) return (lin['1'] ?? 0) <= 0
  const own = path.get(canon(lin))
  if (own) return own.holds
  const flipped = path.get(canonFlip(lin))
  return flipped ? !flipped.holds : undefined
}
const mentions = (t: E | C, name: string): boolean => {
  switch (t.op) {
    case 'var': return t.name === name
    case 'const': return false
    case 'add': case 'sub': case 'min': case 'max': case 'prod': case 'tup': return mentions(t.a, name) || mentions(t.b, name)
    case 'mul': case 'proj': return mentions(t.a, name)
    case 'if': return mentions(t.c, name) || mentions(t.then, name) || mentions(t.else, name)
    case 'get': return mentions(t.key, name)
    case '<': case '<=': case '=': return mentions(t.a, name) || mentions(t.b, name)
    case 'and': case 'or': return t.xs.some(x => mentions(x, name))
    case 'not': return mentions(t.x, name)
    case 'flag': return false
    case 'all': return mentions(t.c, name)
  }
}
// Lean's simpE: each `if` whose condition reads no key and is decided under the path, resolved; nothing else changes.
export function simpE(e: E, path: Path, key: string): E {
  switch (e.op) {
    case 'var': case 'const': return e
    case 'add': case 'sub': case 'min': case 'max': return {op: e.op, a: simpE(e.a, path, key), b: simpE(e.b, path, key)}
    case 'prod': case 'tup': return {op: e.op, a: simpE(e.a, path, key), b: simpE(e.b, path, key)}
    case 'mul': return {op: 'mul', k: e.k, a: simpE(e.a, path, key)}
    case 'proj': return {op: 'proj', k: e.k, a: simpE(e.a, path, key)}
    case 'get': return {op: 'get', map: e.map, key: simpE(e.key, path, key)}
    case 'if': {
      const t = simpE(e.then, path, key), f = simpE(e.else, path, key)
      if (mentions(e.c, key)) return {op: 'if', c: e.c, then: t, else: f}
      const b = truth(e.c, path)
      return b === true ? t : b === false ? f : {op: 'if', c: e.c, then: t, else: f}
    }
  }
}
export const whenPath = (f: FrameCut): Path => new Map(f.when.map(w => [canon(w), {lin: w, holds: true}]))
const same = (a: E, b: E): boolean => JSON.stringify(a) === JSON.stringify(b)
// Lean's frameOk: the two counts share their key, and under `when` their bounds and bodies are the same terms.
export function frameOk(counts: Count[], f: FrameCut): boolean {
  const post = counts.find(c => c.v === f.post), pre = counts.find(c => c.v === f.pre)
  if (!post || !pre || post.key !== pre.key) return false
  const path = whenPath(f)
  return same(simpE(post.below, path, post.key), simpE(pre.below, path, post.key)) && same(simpE(post.body, path, post.key), simpE(pre.body, path, post.key))
}
// Lean's frameRows: post − pre ≤ 0 and pre − post ≤ 0.
export const frameRows = (f: FrameCut): Lin[] => [{[f.post]: 1, [f.pre]: -1}, {[f.pre]: 1, [f.post]: -1}]
const normal = (w: Lin): Lin => (Object.keys(w).every(key => key === '1' || w[key] === 0) ? k(w['1'] ?? 0) : w)
export const frameActive = (f: FrameCut, path: Path): boolean => f.when.every(w => decide(normal(w), path) === true)
// Lean's framePath: the active frames' rows in front of the lemma path. Eligibility reads the original path only.
export function framePath(frames: FrameCut[], lemmas: LemmaCut[], path: Path): Path {
  const base = lemmaPath(lemmas, path), active = frames.filter(f => frameActive(f, path))
  if (!active.length) return base
  const out: Path = new Map()
  let duplicate = 0
  for (const atom of [...active.flatMap(f => frameRows(f).map(lin => ({lin, holds: true}))), ...base.values()]) {
    const id = canon(atom.lin)
    out.set(out.has(id) ? `@${duplicate++}` : id, atom)
  }
  return out
}
// Lean's checkGoalFrames: the lemma-cut checker with the frames' rows at eligible leaves. With no frames it is
// checkGoalLemmas; it never changes a lemma's own check.
export function checkGoalFrames(goal: Goal, counts: Count[], tree: Tree, lemmas: LemmaCut[] = [], frames: FrameCut[] = []): boolean {
  if (!frames.every(f => frameOk(counts, f))) return false
  if (lemmas.length) {
    // Each lemma as kernel.ts checks it: alone, under its own conditions and the negated cut, without frames.
    const alone = (l: LemmaCut): boolean => {
      const hyps = l.slice === undefined ? goal.hyps : l.slice.map(i => goal.hyps[i]!)
      const path: Path = new Map([[canon(l.cut), {lin: l.cut, holds: false}], ...l.when.map(w => [canon(w), {lin: w, holds: true}] as const)])
      return check({...goal, hyps}, l.tree, path)
    }
    if (!lemmas.every(alone)) return false
  }
  const visit = (t: Tree, path: Path): boolean => {
    if ('leaf' in t) return check(goal, t, framePath(frames, lemmas, path))
    const id = canon(t.split)
    if (path.has(id) || Object.keys(t.split).every(key => key === '1')) return false
    return visit(t.yes, new Map(path).set(id, {lin: t.split, holds: true})) && visit(t.no, new Map(path).set(id, {lin: t.split, holds: false}))
  }
  return visit(tree, new Map())
}
