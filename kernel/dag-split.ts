// Untrusted DAG-safe structural interning and per-action @step pre-split.
// Nothing here is trusted: every proof tree constructed is an ordinary kernel
// split tree checked by unmodified kernel/kernel.ts (check / checkLaws), and
// every model returned is verified against all hypotheses of the original goal.
import {type C, type E, walkOnce} from '../core/machine.ts'
import {type Lin, type Step, env, solve} from '../core/solver.ts'
import {checkRefutation} from '../core/check.ts'
import {type Goal, type Path, type Tree, canon, canonFlip, linear, snapshotKernelTermMemo, trueC, truth, withProducts} from './kernel.ts'
import {Reader} from './reader.ts'

// Bottom-up structural DAG interner: assigns structurally equal ASTs the exact
// same integer ID in O(distinct DAG nodes) time and memory without unrolling
// shared subtrees into exponential JSON strings. Stores only shallow signatures
// with child IDs (never retains AST objects in `table`).
export type DagInterner = {
  id(value: unknown): number | undefined
  clear(): void
}

export function dagInterner(): DagInterner {
  let memo = new WeakMap<object, number>()
  let table = new Map<string, number>()
  let next = 0
  const active = new WeakSet<object>()

  const scalar = (v: unknown): string => {
    if (typeof v === 'number') return Object.is(v, -0) ? 'n:-0' : `n:${v}`
    if (typeof v === 'string') return `s:${JSON.stringify(v)}`
    return `p:${String(v)}`
  }

  const encode = (v: unknown): number | undefined => {
    if (!v || typeof v !== 'object') {
      const key = scalar(v)
      let id = table.get(key)
      if (id === undefined) table.set(key, (id = ++next))
      return id
    }
    const hit = memo.get(v)
    if (hit !== undefined) return hit
    if (active.has(v)) return undefined
    active.add(v)
    let key: string
    try {
      if (Array.isArray(v)) {
        const parts = new Array<string>(v.length)
        for (let i = 0; i < v.length; i++) {
          const cid = encode(v[i])
          if (cid === undefined) return undefined
          parts[i] = String(cid)
        }
        key = `[${parts.join(',')}]`
      } else {
        const o = v as Record<string, unknown>
        const ks = Object.keys(o).sort()
        const parts: string[] = []
        for (let i = 0; i < ks.length; i++) {
          const k = ks[i]!
          const val = o[k]
          if (val === undefined) continue
          const cid = encode(val)
          if (cid === undefined) return undefined
          parts.push(`${JSON.stringify(k)}:${cid}`)
        }
        key = `{${parts.join(',')}}`
      }
    } finally {
      active.delete(v)
    }
    let id = table.get(key)
    if (id === undefined) table.set(key, (id = ++next))
    memo.set(v, id)
    return id
  }

  return {
    id: encode,
    clear() {
      memo = new WeakMap()
      table = new Map()
      next = 0
    },
  }
}

// --- Untrusted per-action @step pre-split ----------------------------------------------------------------------------

// Minimum distinct DAG nodes in a root goal before checking for a bounded
// action selector to pre-split. Small goals keep the existing path unchanged.
export const preSplitOn = env.GDP_PRESPLIT !== '0'
export const preSplitTerms = Number(env.GDP_PRESPLIT_TERMS ?? 2_500)
const preSplitTrace = !!env.GDP_PRESPLIT_TRACE

export const preSplitStats = {goals: 0, proven: 0, sat: 0, unknown: 0, skipped: 0}

const FALSE_C: C = {op: '<=', a: {op: 'const', value: 1}, b: {op: 'const', value: 0}}

const countDag = (root: unknown): number => {
  let n = 0
  walkOnce(root, () => { n++ })
  return n
}

// Collect variables with an explicit, unconditional integer upper bound
// 0 <= x <= hi in the root goal's positive top-level conjuncts (e.g. `oneOf`
// emits `action < K`, `upTo` emits `x <= U`, or an explicit equality disjunction).
function rootUpperBounds(goal: Goal): Map<string, number> {
  const hi = new Map<string, number>()
  const bound = (name: string, u: number) => {
    if (!Number.isInteger(u) || u < 1) return
    const prev = hi.get(name)
    if (prev === undefined || u < prev) hi.set(name, u)
  }
  const eqConst = (c: C): [string, number] | undefined => {
    if (c.op !== '=') return undefined
    if (c.a.op === 'var' && c.b.op === 'const' && Number.isInteger(c.b.value) && c.b.value >= 0) return [c.a.name, c.b.value]
    if (c.b.op === 'var' && c.a.op === 'const' && Number.isInteger(c.a.value) && c.a.value >= 0) return [c.b.name, c.a.value]
    return undefined
  }
  const seen = new WeakSet<object>()
  const collect = (c: C, pos: boolean): void => {
    if (seen.has(c)) return
    seen.add(c)
    if (c.op === 'not') { collect(c.x, !pos); return }
    if ((c.op === 'and' && pos) || (c.op === 'or' && !pos)) {
      for (const y of c.xs) collect(y, pos)
      return
    }
    if (pos && c.op === 'or' && c.xs.length >= 2) {
      let varName: string | undefined, maxVal = -1, ok = true
      for (const y of c.xs) {
        const eq = eqConst(y)
        if (!eq || (varName !== undefined && eq[0] !== varName)) { ok = false; break }
        varName = eq[0]
        if (eq[1] > maxVal) maxVal = eq[1]
      }
      if (ok && varName !== undefined && maxVal >= 1) bound(varName, maxVal)
      return
    }
    if (pos) {
      if (c.op === '<=' && c.a.op === 'var' && c.b.op === 'const') bound(c.a.name, c.b.value)
      else if (c.op === '<' && c.a.op === 'var' && c.b.op === 'const' && c.b.value >= 1) bound(c.a.name, c.b.value - 1)
    } else {
      // !(c < x) means x <= c; !(c <= x) means x < c i.e. x <= c - 1
      if (c.op === '<' && c.a.op === 'const' && c.b.op === 'var') bound(c.b.name, c.a.value)
      else if (c.op === '<=' && c.a.op === 'const' && c.b.op === 'var' && c.a.value >= 1) bound(c.b.name, c.a.value - 1)
    }
  }
  for (const h of goal.hyps) collect(h, true)
  return hi
}

const leLin = (sel: string, c: number): Lin => (c === 0 ? {[sel]: 1} : {[sel]: 1, 1: -c})
const ge0Lin = (sel: string): Lin => ({[sel]: -1})

// Build the exact order-encoded path P_k for `sel = k` over `0..U`:
//   [0]: sel <= U (true)
//   [1]: -sel <= 0 (true)
//   [2..2+k-1]: sel <= j (false, i.e. sel >= j + 1)
//   [2+k..2+U-1]: sel <= j (true)   (for k < U)
// Every comparison `sel = j`, `sel <= j`, `sel < j` for j in 0..U is directly
// decided by unmodified `kernel.ts:truth(_, P_k)`.
function orderPath(sel: string, u: number, k: number): Path {
  const p: Path = new Map()
  const hi = leLin(sel, u), g0 = ge0Lin(sel)
  p.set(canon(hi), {lin: hi, holds: true})
  p.set(canon(g0), {lin: g0, holds: true})
  for (let j = 0; j < k; j++) {
    const l = leLin(sel, j)
    p.set(canon(l), {lin: l, holds: false})
  }
  for (let j = k; j < u; j++) {
    const l = leLin(sel, j)
    p.set(canon(l), {lin: l, holds: true})
  }
  return p
}

// DAG-preserving specialization of `goal` under `path` (P_k).
// Only folds conditions that unmodified `kernel.ts:truth(c, path)` itself decides,
// so every linear row produced on the specialized goal is guaranteed to appear in
// the original goal under P_k (with any modified choice terms tracked in `rewritten`).
export function specializeGoal(goal: Goal, path: Path, sel: string, k: number): {goal: Goal, rewritten: Map<E, E>, nodes: number} {
  const eMemo = new WeakMap<E, E>()
  const cCondMemo = new WeakMap<C, C>()
  const cPosMemo = new WeakMap<C, C>()
  const cNegMemo = new WeakMap<C, C>()
  const rewritten = new Map<E, E>()

  const specE = (e: E): E => {
    const hit = eMemo.get(e)
    if (hit) return hit
    let out: E = e
    switch (e.op) {
      case 'var': case 'const': break
      case 'mul': {
        const a = specE(e.a)
        if (a !== e.a) out = {...e, a}
        break
      }
      case 'proj': {
        const a = specE(e.a)
        if (a !== e.a) out = {...e, a}
        break
      }
      case 'get': {
        const key = specE(e.key)
        if (key !== e.key) out = {...e, key}
        break
      }
      case 'add': case 'sub': case 'min': case 'max': case 'prod': case 'tup': {
        const a = specE(e.a), b = specE(e.b)
        if (a !== e.a || b !== e.b) {
          out = {...e, a, b}
          if (e.op === 'sub' || e.op === 'min' || e.op === 'max') rewritten.set(out, e)
        }
        break
      }
      case 'if': {
        const t = truth(e.c, path)
        if (t === true) out = specE(e.then)
        else if (t === false) out = specE(e.else)
        else {
          const c = specCond(e.c), th = specE(e.then), el = specE(e.else)
          if (c !== e.c || th !== e.then || el !== e.else) {
            out = {op: 'if', c, then: th, else: el}
            rewritten.set(out, e)
          }
        }
        break
      }
    }
    eMemo.set(e, out)
    return out
  }

  // Condition inside an `if` guard (only its Kleene truth matters).
  const specCond = (c: C): C => {
    const hit = cCondMemo.get(c)
    if (hit) return hit
    const t = truth(c, path)
    let out: C = c
    if (t === true) out = trueC
    else if (t === false) out = FALSE_C
    else {
      switch (c.op) {
        case 'flag': case 'all': break
        case 'not': {
          const x = specCond(c.x)
          if (x !== c.x) out = {op: 'not', x}
          break
        }
        case 'and': case 'or': {
          const dom = c.op === 'or'
          const xs: C[] = []
          let changed = false
          for (const y of c.xs) {
            const ty = truth(y, path)
            if (ty === dom) { out = dom ? trueC : FALSE_C; cCondMemo.set(c, out); return out }
            if (ty === !dom) { changed = true; continue }
            const sy = specCond(y)
            if (sy !== y) changed = true
            xs.push(sy)
          }
          if (xs.length === 0) out = dom ? FALSE_C : trueC
          else if (xs.length === 1) out = xs[0]!
          else if (changed) out = {op: c.op, xs}
          break
        }
        case '<': case '<=': case '=': {
          const a = specE(c.a), b = specE(c.b)
          if (a !== c.a || b !== c.b) out = {...c, a, b}
          break
        }
      }
    }
    cCondMemo.set(c, out)
    return out
  }

  // Hypothesis condition in positive (`pos=true`) or negated (`pos=false`) context.
  // Preserves exact linear facts of unmodified `kernel.ts:facts(c, path, pos)`.
  const specH = (c: C, pos: boolean): C => {
    const bag = pos ? cPosMemo : cNegMemo
    const hit = bag.get(c)
    if (hit) return hit
    let out: C = c
    switch (c.op) {
      case 'flag': case 'all': break
      case 'not': {
        const x = specH(c.x, !pos)
        if (x !== c.x) out = {op: 'not', x}
        break
      }
      case 'and': case 'or': {
        if ((c.op === 'and') === pos) {
          // Conjunction context: keep any falsifying child immediately, drop children
          // already forced true by P_k (their atoms are already on P_k).
          const xs: C[] = []
          let changed = false
          for (const y of c.xs) {
            const ty = truth(y, path)
            if (ty === !pos) {
              out = specH(y, pos)
              bag.set(c, out)
              return out
            }
            if (ty === pos) { changed = true; continue }
            const sy = specH(y, pos)
            if (sy !== y) changed = true
            xs.push(sy)
          }
          if (xs.length === 0) out = pos ? trueC : FALSE_C
          else if (xs.length === 1) out = xs[0]!
          else if (changed) out = {op: c.op, xs}
        } else {
          // Disjunction context: matches `kernel.ts:373` filtering out `!pos` children.
          const xs: C[] = []
          let changed = false
          for (const y of c.xs) {
            if (truth(y, path) === !pos) { changed = true; continue }
            const sy = specH(y, pos)
            if (sy !== y) changed = true
            xs.push(sy)
          }
          if (xs.length === 0) out = pos ? FALSE_C : trueC
          else if (xs.length === 1) out = xs[0]!
          else if (changed) out = {op: c.op, xs}
        }
        break
      }
      case '<': case '<=': case '=': {
        const a = specE(c.a), b = specE(c.b)
        if (a !== c.a || b !== c.b) out = {...c, a, b}
        break
      }
    }
    bag.set(c, out)
    return out
  }

  const last = goal.hyps.length - 1
  const eqSel: C = {op: '=', a: {op: 'var', name: sel}, b: {op: 'const', value: k}}
  const hyps: C[] = [eqSel]
  for (let i = 0; i < last; i++) {
    const h = specH(goal.hyps[i]!, true)
    if (h !== trueC) hyps.push(h)
  }
  if (last >= 0) hyps.push(specH(goal.hyps[last]!, true))
  const outGoal: Goal = {name: `${goal.name} [${sel}=${k}]`, hyps, ...(goal.wordDivision ? {wordDivision: true} : {})}
  return {goal: outGoal, rewritten, nodes: countDag(hyps)}
}

// Identify a bounded selector variable whose values genuinely simplify the DAG.
export function findSelector(goal: Goal, origNodes: number): {sel: string, hi: number} | undefined {
  const bounds = rootUpperBounds(goal)
  if (!bounds.size) return undefined
  const tested = new Map<string, Set<number>>()
  const hits = new Map<string, number>()
  walkOnce(goal.hyps, o => {
    const x = o as {op?: string, a?: E, b?: E}
    if (x.op !== '=' || !x.a || !x.b) return
    let name: string | undefined, val: number | undefined
    if (x.a.op === 'var' && x.b.op === 'const') { name = x.a.name; val = x.b.value }
    else if (x.b.op === 'var' && x.a.op === 'const') { name = x.b.name; val = x.a.value }
    if (name === undefined || val === undefined) return
    const u = bounds.get(name)
    if (u === undefined || val < 0 || val > u) return
    let s = tested.get(name)
    if (!s) tested.set(name, (s = new Set()))
    s.add(val)
    hits.set(name, (hits.get(name) ?? 0) + 1)
  })
  const cands = [...tested.entries()]
    .filter(([name, s]) => s.size >= 2 && bounds.get(name)! <= 63)
    .sort((a, b) => (b[1].size - a[1].size) || ((hits.get(b[0]) ?? 0) - (hits.get(a[0]) ?? 0)) || (bounds.get(a[0])! - bounds.get(b[0])!))
  for (const [sel, vals] of cands.slice(0, 3)) {
    const hi = bounds.get(sel)!
    const sorted = [...vals].sort((a, b) => a - b)
    const sample = [...new Set([sorted[0]!, sorted[sorted.length >> 1]!, sorted[sorted.length - 1]!])]
    let sum = 0, minNodes = Infinity
    for (const v of sample) {
      const n = specializeGoal(goal, orderPath(sel, hi, v), sel, v).nodes
      sum += n
      if (n < minNodes) minNodes = n
    }
    const mean = sum / sample.length
    if (mean <= 0.70 * origNodes && (mean * (hi + 1) <= 2.2 * origNodes || minNodes <= 0.25 * origNodes)) return {sel, hi}
  }
  return undefined
}

// Incremental trail + Reader wrapper so widening a multi-leaf proof tree back
// onto a large monolithic goal updates changed sub-DAGs in O(delta) per leaf
// rather than re-evaluating leafConstraints(whole, wp) from scratch at every leaf.
type TrailEntry = {name: string, lin: Lin, holds: boolean}
class ReaderTrail {
  readonly stack: TrailEntry[] = []
  readonly on = new Map<string, {val: boolean, at: number}>()
  readonly stamps: number[] = []
  private stampN = 0
  readonly reader: Reader
  constructor(goal: Goal) {
    this.reader = new Reader(goal, {
      get: name => this.on.get(name),
      stamp: at => this.stamps[at]!,
      size: () => this.stack.length,
      lin: at => this.stack[at]!,
    })
  }
  push(name: string, lin: Lin, holds: boolean): boolean {
    if (this.on.has(name)) return false
    this.on.set(name, {val: holds, at: this.stack.length})
    this.stamps[this.stack.length] = ++this.stampN
    this.stack.push({name, lin, holds})
    this.reader.touch(name)
    return true
  }
  pop(): void {
    const name = this.stack.pop()!.name
    this.on.delete(name)
    this.reader.touch(name)
  }
  toPath(): Path {
    const p: Path = new Map()
    for (const x of this.stack) p.set(x.name, {lin: x.lin, holds: x.holds})
    return p
  }
  leafRows(): ReturnType<Reader['leafRows']> {
    this.reader.begin()
    return this.reader.leafRows()
  }
}

// Widen a per-action tree `tree` (proved for `part` at empty path) back onto
// `(whole, rootWp)` where `rootWp = P_k`, using incremental Reader trails so
// multi-leaf trees avoid O(leaves * |whole|) leafConstraints recomputation.
function widenToWhole(
  part: Goal,
  whole: Goal,
  tree: Tree,
  opaque: Record<string, E>,
  rootWp: Path,
  wt: ReaderTrail,
  pastWall: () => boolean,
  fallback: (g: Goal, p: Path) => Tree | undefined,
): Tree | undefined {
  const names = Object.keys(opaque)
  const pt = new ReaderTrail(part)
  let pushedRoot = 0
  for (const [key, a] of rootWp) {
    if (wt.push(key, a.lin, a.holds)) pushedRoot++
  }

  const rename = (lin: Lin, wpCache: {p?: Path}): Lin | undefined => {
    if (!names.length) return lin
    const out: Lin = {}
    for (const [key, coef] of Object.entries(lin)) {
      const e = opaque[key]
      if (e) {
        const wp = (wpCache.p ??= wt.toPath())
        const l = linear(e, wp)
        if (!l) return undefined
        for (const [k2, c2] of Object.entries(l)) {
          const next = (out[k2] ?? 0) + c2 * coef
          if (!Number.isSafeInteger(next)) return undefined
          if (next === 0) delete out[k2]
          else out[k2] = next
        }
      } else if (names.some(n => key.includes(n))) {
        return undefined
      } else {
        const next = (out[key] ?? 0) + coef
        if (next === 0) delete out[key]
        else out[key] = next
      }
    }
    return out
  }

  const go = (node: Tree): Tree | undefined => {
    if (pastWall()) return undefined
    const wpCache: {p?: Path} = {}
    if (!('leaf' in node)) {
      const id = canon(node.split), wl = rename(node.split, wpCache)
      if (!wl) return fallback(whole, wt.toPath())
      const wid = canon(wl)
      const known = Object.keys(wl).every(key => key === '1')
        ? (wl['1'] ?? 0) <= 0
        : wt.on.has(wid) ? wt.on.get(wid)!.val
        : wt.on.has(canonFlip(wl)) ? !wt.on.get(canonFlip(wl))!.val
        : undefined
      if (known !== undefined) {
        const pushedP = pt.push(id, node.split, known)
        try { return go(known ? node.yes : node.no) } finally { if (pushedP) pt.pop() }
      }
      let yes: Tree | undefined
      const pYes = pt.push(id, node.split, true)
      const wYes = wt.push(wid, wl, true)
      try { yes = go(node.yes) } finally { if (wYes) wt.pop(); if (pYes) pt.pop() }
      if (!yes) return undefined
      let no: Tree | undefined
      const pNo = pt.push(id, node.split, false)
      const wNo = wt.push(wid, wl, false)
      try { no = go(node.no) } finally { if (wNo) wt.pop(); if (pNo) pt.pop() }
      return no ? {split: wl, yes, no} : undefined
    }
    const rp = pt.leafRows()
    if (pastWall()) return undefined
    const rw = wt.leafRows()
    const at = new Map<string, number>()
    rw.forEach((r, i) => { const key = canon(r.lin); if (!at.has(key)) at.set(key, i) })
    const map = (i: number) => {
      if (i >= rp.length) return i - rp.length + rw.length
      const l = rename(rp[i]!.lin, wpCache)
      return l && at.get(canon(l))
    }
    const leaf: Step[] = []
    const products: [number, number][] = []
    const squares = (node.squares ?? []).map(s => rename(s, wpCache))
    let ok = squares.every(Boolean)
    for (const st of ok ? node.leaf : []) {
      if (st.kind !== 'input') { leaf.push(st); continue }
      const j = map(st.index)
      if (j === undefined) { ok = false; break }
      leaf.push({...st, index: j})
    }
    for (const [i, j] of ok ? node.products ?? [] : []) {
      const pi = map(i), pj = map(j)
      if (pi === undefined || pj === undefined) { ok = false; break }
      products.push([pi, pj])
    }
    if (ok && names.length && !checkRefutation(withProducts(rw, products, squares as Lin[]), leaf)) ok = false
    if (ok) return {leaf, ...(node.products ? {products} : {}), ...(node.squares ? {squares: squares as Lin[]} : {})}
    const absurd = rw.findIndex(r => Object.keys(r.lin).every(key => key === '1') && (r.lin['1'] ?? 0) > 0)
    if (absurd >= 0) return {leaf: [{kind: 'input', index: absurd}]}
    return fallback(whole, wt.toPath())
  }

  try {
    return go(tree)
  } finally {
    for (let i = 0; i < pushedRoot; i++) wt.pop()
  }
}

export type PreSplitOutcome =
  | {tree: Tree, nodes: number}
  | {stuck: 'sat' | 'unknown', witness?: Record<string, number>, path: Path, why?: string}

export type PreSplitDeps = {
  origNodes: number
  budget: {nodes: number, until?: number}
  clock: () => number
  withinDeadline: (until: number) => number
  pastWall: () => boolean
  late: (until: number) => boolean
  searchWork: () => number
  searchWorkCap: () => number
  withSearchWork: <T>(cap: number, f: () => T) => T
  growSub: (g: Goal, until: number) => PreSplitOutcome
  growFallback: (g: Goal, p: Path) => Tree | undefined
  brokenOf: (g: Goal) => (w: Record<string, number>, ids?: number[], first?: boolean) => number[]
}

export function preSplitBySelector(goal: Goal, deps: PreSplitDeps): PreSplitOutcome | undefined {
  const picked = findSelector(goal, deps.origNodes)
  if (!picked) { preSplitStats.skipped++; return undefined }
  const {sel, hi} = picked
  const count = hi + 1
  const hiAtom = leLin(sel, hi), g0Atom = ge0Lin(sel)
  preSplitStats.goals++

  // Specialize each action k = 0..hi into its own compact DAG goal.
  const tSpec0 = preSplitTrace ? deps.clock() : 0
  type Case = {k: number, path: Path, part?: Goal, rewritten?: Map<E, E>, nodes: number, tree?: Tree}
  const cases: Case[] = []
  for (let k = 0; k < count; k++) {
    const path = orderPath(sel, hi, k)
    const spec = specializeGoal(goal, path, sel, k)
    cases.push({k, path, part: spec.goal, rewritten: spec.rewritten, nodes: spec.nodes})
  }
  if (preSplitTrace) {
    console.error(`[presplit] ${goal.name}: sel=${sel} in 0..${hi}, origDag=${deps.origNodes}, specMs=${Math.round(deps.clock() - tSpec0)}, cases=${cases.map(c => `${c.k}:${c.nodes}`).join(' ')}`)
  }

  // Share the single goal's budget across all K actions rather than multiplying
  // the default per-goal budget by K when budget.until is unset.
  const defaultGoalMs = Math.max(20_000, goal.hyps.length * 1000)
  const goalEnd = deps.withinDeadline(deps.budget.until ?? (deps.clock() + defaultGoalMs))

  // Lazily construct one ReaderTrail on `goal` reused across every proved action's
  // widening pass and the final outer range guards (`sel <= hi`, `-sel <= 0`).
  let wholeTrail: ReaderTrail | undefined
  const getWholeTrail = (): ReaderTrail => (wholeTrail ??= new ReaderTrail(goal))

  // Solve smallest specialized DAGs first so trivial/identity actions clear in ms
  // and fast 1-step CTIs are caught early. Pass 1 gives each case a fair slice so
  // one hard action cannot starve an easy SAT action; Pass 2 gives unfinished cases
  // the full remaining budget.
  const order = [...cases].sort((a, b) => a.nodes - b.nodes || a.k - b.k)
  const totalSpecNodes = cases.reduce((acc, c) => acc + c.nodes, 0)
  const verifyWitness = deps.brokenOf(goal)
  const countLeaves = (t: Tree): number => ('leaf' in t ? 1 : countLeaves(t.yes) + countLeaves(t.no))
  let totalNodes = 0
  let provenCount = 0
  let firstUnknown: PreSplitOutcome | undefined

  for (const pass of [1, 2] as const) {
    const pending = order.filter(c => !c.tree)
    if (!pending.length) break
    let left = pending.length
    let passTried = 0
    for (const c of pending) {
      if (deps.pastWall() || deps.late(goalEnd)) {
        preSplitStats.unknown++
        return firstUnknown ?? {stuck: 'unknown', path: c.path, why: 'pre-split budget exhausted'}
      }
      const now = deps.clock(), end = deps.withinDeadline(goalEnd)
      const w = deps.searchWork(), wCap = deps.searchWorkCap()
      const share = pass === 1 ? 1 / Math.max(1, left) : 1
      const subUntil = end === Infinity ? Infinity : now + share * Math.max(0, end - now)
      const subWorkCap = wCap === Infinity ? Infinity : w + share * Math.max(0, wCap - w)
      left--
      passTried++

      const tSolve0 = preSplitTrace ? deps.clock() : 0
      const part = c.part!
      const out = deps.withSearchWork(subWorkCap, () => deps.growSub(part, subUntil))
      const solveMs = preSplitTrace ? Math.round(deps.clock() - tSolve0) : 0
      if ('tree' in out) {
        totalNodes += out.nodes
        const tWiden0 = preSplitTrace ? deps.clock() : 0
        // Map only rewritten choice terms that actually received a kernel termColumn ID.
        const opaque: Record<string, E> = {}
        if (c.rewritten?.size) {
          for (const [rew, orig] of c.rewritten) {
            const tid = snapshotKernelTermMemo(rew)
            if (tid !== undefined) opaque[`⟦${tid}⟧`] = orig
          }
        }
        const widened = widenToWhole(part, goal, out.tree, opaque, c.path, getWholeTrail(), deps.pastWall, deps.growFallback)
        if (preSplitTrace) {
          console.error(`[presplit]   p${pass} k=${c.k} nodes=${c.nodes} PROVEN solveMs=${solveMs} leaves=${countLeaves(out.tree)} widenMs=${Math.round(deps.clock() - tWiden0)} ok=${!!widened}`)
        }
        if (!widened) {
          preSplitStats.unknown++
          return {stuck: 'unknown', path: c.path, why: 'pre-split widen failed'}
        }
        c.tree = widened
        c.part = undefined
        c.rewritten = undefined
        provenCount++
        continue
      }
      if (out.stuck === 'sat' && out.witness) {
        const wFull = {...out.witness, [sel]: c.k}
        const bad = verifyWitness(wFull, undefined, true)
        if (preSplitTrace) {
          console.error(`[presplit]   p${pass} k=${c.k} nodes=${c.nodes} SAT solveMs=${solveMs} verified=${bad.length === 0}`)
        }
        if (!bad.length) {
          preSplitStats.sat++
          return {stuck: 'sat', witness: wFull, path: new Map(), why: out.why ?? 'a model'}
        }
      } else if (preSplitTrace) {
        console.error(`[presplit]   p${pass} k=${c.k} nodes=${c.nodes} ${out.stuck.toUpperCase()} solveMs=${solveMs} why=${out.why ?? ''}`)
      }
      firstUnknown ??= {stuck: 'unknown', path: c.path, why: out.why}
      // If the smallest 2 actions both stall without proving or finding SAT and
      // specialization did not tightly partition the DAG, bail out early so the
      // caller can fall back to the monolithic solver.
      if (pass === 1 && count >= 4 && passTried >= 2 && provenCount === 0 && totalSpecNodes > 1.5 * deps.origNodes) {
        if (preSplitTrace) console.error(`[presplit]   bailing out after ${passTried} stalled smallest cases`)
        preSplitStats.skipped++
        return undefined
      }
      if (pass === 2) {
        preSplitStats.unknown++
        return firstUnknown
      }
    }
  }

  if (cases.some(c => !c.tree)) {
    preSplitStats.unknown++
    return firstUnknown ?? {stuck: 'unknown', path: new Map(), why: 'pre-split unfinished'}
  }

  // Verify outer range guards `sel <= hi` and `-sel <= 0` refute their failing
  // sides on the original goal using the reused ReaderTrail.
  const wt = getWholeTrail()
  const hiId = canon(hiAtom), g0Id = canon(g0Atom)
  wt.push(hiId, hiAtom, false)
  const noHiRes = solve(wt.leafRows())
  wt.pop()
  if (noHiRes.kind !== 'refuted') { preSplitStats.skipped++; return undefined }
  const noHiLeaf: Tree = {leaf: noHiRes.steps}

  wt.push(hiId, hiAtom, true)
  wt.push(g0Id, g0Atom, false)
  const noG0Res = solve(wt.leafRows())
  wt.pop()
  wt.pop()
  if (noG0Res.kind !== 'refuted') { preSplitStats.skipped++; return undefined }
  const noG0Leaf: Tree = {leaf: noG0Res.steps}

  // Stitch all K widened action trees into one standard kernel split tree.
  // Path layout along the chain:
  //   idx 0: sel <= hi (true)
  //   idx 1: -sel <= 0 (true)
  //   idx 2..2+k-1: sel <= j (false)
  //   idx 2+k: sel <= k (true, for k < hi)
  //   idx 2+m (m = k+1..hi-1): sel <= m (true); its `no` side has `m+1 - sel <= 0`
  //     at idx `2+m`, contradicting `sel - k <= 0` at idx `2+k` in a 3-step Farkas leaf!
  let chain: Tree = cases[hi]!.tree!
  for (let k = hi - 1; k >= 0; k--) {
    let branch: Tree = cases[k]!.tree!
    const idxK = 2 + k
    for (let m = hi - 1; m > k; m--) {
      const idxM = 2 + m
      const deadLeaf: Tree = {leaf: [{kind: 'input', index: idxK}, {kind: 'input', index: idxM}, {kind: 'combine', a: 0, b: 1, ma: 1, mb: 1}]}
      branch = {split: leLin(sel, m), yes: branch, no: deadLeaf}
    }
    chain = {split: leLin(sel, k), yes: branch, no: chain}
  }
  const stitched: Tree = {split: hiAtom, yes: {split: g0Atom, yes: chain, no: noG0Leaf}, no: noHiLeaf}
  preSplitStats.proven++
  return {tree: stitched, nodes: totalNodes}
}
