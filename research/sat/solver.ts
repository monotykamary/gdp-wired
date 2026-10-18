// CDCL: two watched literals with blockers (binary clauses watched by their other literal alone), first-UIP learning
// with recursive minimization, VSIDS on a binary heap with phase saving, glucose-style (or Luby) restarts, and periodic
// deletion of learned clauses with many decision levels (LBD). Clauses live in one Int32Array arena, literals coded as
// 2v (v true) and 2v + 1 (v false). The interface speaks DIMACS literals (nonzero integers). Every answer carries
// evidence check.ts and lrat.ts verify:
//   sat      a model (model[v] for v = 1..vars)
//   unsat    a DRUP proof: the learned clauses in the order learned, deletions as {d: clause}, then the empty clause;
//            each learned clause follows by unit propagation alone from the clauses not yet deleted before it
//            and the same refutation as LRAT (lrat.ts): input clause i has id i + 1; each lemma gets the next id and
//            names its hints, the clauses that, in order, become unit and then falsified once its literals are false;
//            literals fixed at level 0 become unit lemmas of their own, so later hints name one clause for each
//   unknown  the conflict budget ran out
// solver-v1.ts is the previous version (arrays of arrays, a linear scan per decision), kept for comparison.
export type Clause = number[]
export type Step = Clause | {d: Clause}
export type LratStep = {id: number, clause: Clause, hints: number[]} | {del: number[]}
export type Result = {kind: 'sat', model: boolean[]} | {kind: 'unsat', proof: Step[], lrat: LratStep[]} | {kind: 'unknown', conflicts: number}
// Tuning: lubyUnit conflicts per Luby step (restarts 'luby'), emaMargin how far the recent LBD average must exceed the
// long one for a restart (restarts 'ema', glucose-style, the default: on the multipliers and pigeonholes it beat Luby
// at every unit tried, see runs/sat-bench.md), drup: false records only the LRAT proof (proof is then just the empty clause), decay of VSIDS bumps, the first reduction after reduceBase conflicts and each
// later one reduceInc more apart.
export type Options = {limit?: number, minimize?: boolean, reduce?: boolean, restarts?: 'luby' | 'ema', lubyUnit?: number, decay?: number, reduceBase?: number, reduceInc?: number, emaMargin?: number, drup?: boolean}

// Only the lemmas the empty clause depends on, through hints, and deletions of those: a smaller proof of the same thing.
const trim = (lrat: LratStep[]): LratStep[] => {
  const used = new Set<number>([(lrat.at(-1) as {id: number}).id])
  for (let i = lrat.length - 1; i >= 0; i--) { const s = lrat[i]!; if ('id' in s && used.has(s.id)) for (const h of s.hints) used.add(h) }
  return lrat.flatMap<LratStep>(s => ('id' in s ? (used.has(s.id) ? [s] : []) : (s.del.some(id => used.has(id)) ? [{del: s.del.filter(id => used.has(id))}] : [])))
}

const luby = (i: number): number => {
  let k = 1
  while ((1 << k) - 1 < i) k++
  return (1 << k) - 1 === i ? 1 << (k - 1) : luby(i - (1 << (k - 1)) + 1)
}

const code = (d: number) => (d > 0 ? 2 * d : -2 * d + 1)
const dimacs = (L: number) => (L & 1 ? -(L >> 1) : L >> 1)

export function solve(vars: number, input: Clause[], {limit = Infinity, minimize = true, reduce = true, restarts: restartPolicy = 'ema', lubyUnit = 100, decay = 0.95, reduceBase = 2000, reduceInc = 300, emaMargin = 1.25, drup = true}: Options = {}): Result {
  const proof: Step[] = [], lrat: LratStep[] = []
  let nextId = input.length + 1
  const lemma = (clause: Clause, hints: number[]) => (lrat.push({id: nextId, clause, hints}), nextId++)
  const nLits = 2 * vars + 2
  const lval = new Int8Array(nLits) // per literal: 1 true, -1 false, 0 unassigned
  const level = new Int32Array(vars + 1), reason = new Int32Array(vars + 1).fill(-1), pos = new Int32Array(vars + 1)
  const phase = new Int8Array(vars + 1).fill(1) // the sign bit last assigned (1 = false); first tried false, as v1
  const seen = new Uint8Array(vars + 1), redundant = new Int8Array(vars + 1)
  const unitId = new Int32Array(vars + 1), mark = new Int32Array(vars + 1), levelStamp = new Int32Array(vars + 2)
  let stamp = 0, fixed = 0

  // The arena: clause ci's literals are arena[start[ci] .. start[ci] + size[ci]).
  let arena = new Int32Array(1 << 16), arenaTop = 0
  let start = new Int32Array(1 << 12), size = new Int32Array(1 << 12), cid = new Int32Array(1 << 12), clbd = new Int32Array(1 << 12)
  let deleted = new Uint8Array(1 << 12)
  let nClauses = 0
  const learnts: number[] = []
  const grow = <T extends Int32Array | Uint8Array>(a: T, need: number): T => { if (need <= a.length) return a; const b = new (a.constructor as any)(Math.max(need, a.length * 2)); b.set(a); return b }
  const addClause = (lits: ArrayLike<number>, n: number, id: number): number => {
    arena = grow(arena, arenaTop + n)
    if (nClauses + 1 > start.length) { const m = (nClauses + 1) * 2; start = grow(start, m); size = grow(size, m); cid = grow(cid, m); clbd = grow(clbd, m); deleted = grow(deleted, m) }
    const ci = nClauses++
    start[ci] = arenaTop; size[ci] = n; cid[ci] = id; deleted[ci] = 0
    for (let j = 0; j < n; j++) arena[arenaTop + j] = lits[j]!
    arenaTop += n
    return ci
  }
  const clauseDimacs = (ci: number) => { const s = start[ci]!, out: number[] = new Array(size[ci]!); for (let j = 0; j < size[ci]!; j++) out[j] = dimacs(arena[s + j]!); return out }

  // Watch lists: per literal L, the clauses watching L, as pairs (ci << 1 | binary, blocker) in a growable Int32Array.
  const wdata: Int32Array[] = Array.from({length: nLits}, () => new Int32Array(8)), wlen = new Int32Array(nLits)
  const watch = (L: number, entry: number, blocker: number) => {
    let d = wdata[L]!
    if (wlen[L]! + 2 > d.length) { const e = new Int32Array(d.length * 2); e.set(d); wdata[L] = d = e }
    d[wlen[L]!] = entry; d[wlen[L]! + 1] = blocker; wlen[L]! += 2
  }
  const attach = (ci: number) => {
    const s = start[ci]!, a = arena[s]!, b = arena[s + 1]!, bin = size[ci] === 2 ? 1 : 0
    watch(a, (ci << 1) | bin, b); watch(b, (ci << 1) | bin, a)
  }

  // VSIDS: a max-heap of variables by activity.
  const activity = new Float64Array(vars + 1), heap = new Int32Array(vars + 1), hpos = new Int32Array(vars + 1).fill(-1)
  let hsize = 0, bump = 1
  const up = (i: number) => {
    const v = heap[i]!, a = activity[v]!
    while (i > 0) { const p = (i - 1) >> 1, pv = heap[p]!; if (activity[pv]! >= a) break; heap[i] = pv; hpos[pv] = i; i = p }
    heap[i] = v; hpos[v] = i
  }
  const down = (i: number) => {
    const v = heap[i]!, a = activity[v]!
    for (;;) {
      let c = 2 * i + 1
      if (c >= hsize) break
      if (c + 1 < hsize && activity[heap[c + 1]!]! > activity[heap[c]!]!) c++
      if (activity[heap[c]!]! <= a) break
      heap[i] = heap[c]!; hpos[heap[i]!] = i; i = c
    }
    heap[i] = v; hpos[v] = i
  }
  const insert = (v: number) => { if (hpos[v]! >= 0) return; heap[hsize] = v; hpos[v] = hsize++; up(hsize - 1) }
  const popMax = () => { const v = heap[0]!; hpos[v] = -1; if (--hsize > 0) { heap[0] = heap[hsize]!; hpos[heap[0]!] = 0; down(0) } return v }
  const bumpVar = (v: number) => {
    activity[v]! += bump
    if (activity[v]! > 1e100) { for (let y = 1; y <= vars; y++) activity[y]! *= 1e-100; bump *= 1e-100 }
    if (hpos[v]! >= 0) up(hpos[v]!)
  }
  for (let v = vars; v >= 1; v--) insert(v)

  const trail = new Int32Array(vars + 1), limits = new Int32Array(vars + 1)
  const reachedPos = new Int32Array(vars + 1), stack = new Int32Array(vars + 1) // hintsFor's scratch: each variable once
  let trailLen = 0, nLevels = 0, head = 0

  const assign = (L: number, why: number) => {
    const v = L >> 1
    lval[L] = 1; lval[L ^ 1] = -1
    level[v] = nLevels; reason[v] = why; pos[v] = trailLen
    trail[trailLen++] = L
  }
  // Propagates the trail; returns a conflicting clause's index, or −1.
  const propagate = (): number => {
    while (head < trailLen) {
      const F = trail[head++]! ^ 1 // the literal just made false
      const d = wdata[F]!, n = wlen[F]!
      let i = 0, j = 0
      while (i < n) {
        const entry = d[i]!, blk = d[i + 1]!
        i += 2
        if (lval[blk] === 1) { d[j++] = entry; d[j++] = blk; continue }
        const ci = entry >> 1
        if (entry & 1) { // binary: the blocker is the other literal
          d[j++] = entry; d[j++] = blk
          if (lval[blk] === -1) { while (i < n) d[j++] = d[i++]!; wlen[F] = j; return ci }
          assign(blk, ci)
          continue
        }
        const s = start[ci]!
        if (arena[s] === F) { arena[s] = arena[s + 1]!; arena[s + 1] = F }
        const first = arena[s]!
        if (first !== blk && lval[first] === 1) { d[j++] = entry; d[j++] = first; continue }
        const end = s + size[ci]!
        let moved = false
        for (let k = s + 2; k < end; k++) {
          const L = arena[k]!
          if (lval[L] !== -1) { arena[s + 1] = L; arena[k] = F; watch(L, entry, first); moved = true; break }
        }
        if (moved) continue
        d[j++] = entry; d[j++] = first
        if (lval[first] === -1) { while (i < n) d[j++] = d[i++]!; wlen[F] = j; return ci }
        assign(first, ci)
      }
      wlen[F] = j
    }
    return -1
  }
  const backjump = (to: number) => {
    if (nLevels <= to) return
    const keep = limits[to]!
    for (let t = trailLen - 1; t >= keep; t--) {
      const L = trail[t]!, v = L >> 1
      phase[v] = L & 1
      lval[L] = 0; lval[L ^ 1] = 0
      reason[v] = -1
      insert(v)
    }
    trailLen = keep; head = keep; nLevels = to
  }
  const unsat = (hints: number[]) => (proof.push([]), lemma([], hints), {kind: 'unsat' as const, proof, lrat: trim(lrat)})
  // Level 0: each literal propagated there becomes a unit lemma (the units of its reason's other literals, then the
  // reason), so a hint about it is one clause.
  const fix = () => {
    for (; fixed < trailLen; fixed++) {
      const L = trail[fixed]!, v = L >> 1
      if (unitId[v] !== 0) continue
      const r = reason[v]!, s = start[r]!, hints: number[] = []
      for (let k = s; k < s + size[r]!; k++) if (arena[k] !== L) hints.push(unitId[arena[k]! >> 1]!)
      hints.push(cid[r]!)
      unitId[v] = lemma([dimacs(L)], hints)
    }
  }
  // A conflict at level 0: every literal of the clause is fixed false.
  const refute = (ci: number) => {
    fix()
    const s = start[ci]!, hints: number[] = []
    for (let k = s; k < s + size[ci]!; k++) hints.push(unitId[arena[k]! >> 1]!)
    hints.push(cid[ci]!)
    return unsat(hints)
  }
  // A learned clause's hints: level-0 units first, then the reasons of every literal reached from the conflict that
  // isn't in the learned clause, in trail order, the conflicting clause last.
  const hintsFor = (learned: Int32Array, n: number, ci: number): number[] => {
    stamp++
    for (let t = 0; t < n; t++) mark[learned[t]! >> 1] = stamp
    const units: number[] = []
    let nReached = 0, sp = 0
    stack[sp++] = ci
    while (sp > 0) {
      const c = stack[--sp]!, s = start[c]!
      for (let k = s; k < s + size[c]!; k++) {
        const v = arena[k]! >> 1
        if (mark[v] === stamp) continue
        mark[v] = stamp
        if (level[v] === 0) units.push(unitId[v]!)
        else if (reason[v]! < 0) throw new Error('a decision outside the learned clause')
        else (reachedPos[nReached++] = pos[v]!, stack[sp++] = reason[v]!)
      }
    }
    // Trail order: sort the positions (a native numeric sort), then read each position's variable off the trail.
    const order = reachedPos.subarray(0, nReached).sort()
    const out = units
    for (let t = 0; t < nReached; t++) out.push(cid[reason[trail[order[t]!]! >> 1]!]!)
    out.push(cid[ci]!)
    return out
  }

  // Input clauses: duplicates dropped, tautologies skipped, units assigned at once.
  let buf = new Int32Array(64)
  for (let i = 0; i < input.length; i++) {
    const c = [...new Set(input[i]!)]
    if (c.some(l => c.includes(-l))) continue
    if (c.length === 0) return unsat([i + 1])
    if (c.length === 1) {
      const L = code(c[0]!), v = L >> 1
      if (lval[L] === -1) return unsat([unitId[v]!, i + 1])
      if (lval[L] === 0) (assign(L, -1), unitId[v] = i + 1)
      continue
    }
    if (c.length > buf.length) buf = new Int32Array(c.length * 2)
    for (let j = 0; j < c.length; j++) buf[j] = code(c[j]!)
    attach(addClause(buf, c.length, i + 1))
  }
  { const ci = propagate(); if (ci >= 0) return refute(ci) }
  fix()

  let conflicts = 0, restarts = 0, nextRestart = lubyUnit * luby(1), reductions = 0, nextReduce = reduceBase, sinceRestart = 0
  let emaFast = 0, emaSlow = 0
  let learned = new Int32Array(Math.max(16, vars + 1))
  const touched: number[] = [], inClause: number[] = []
  // Minimization: a literal is redundant when its reason's other literals are, recursively, in the clause or at level 0.
  const implied = (v: number, depth: number): boolean => {
    if (redundant[v] !== 0) return redundant[v] === 1
    const r = reason[v]!
    let ok = r >= 0 && depth < 64
    if (ok) {
      const s = start[r]!
      for (let k = s; k < s + size[r]!; k++) {
        const y = arena[k]! >> 1
        if (y === v || level[y] === 0 || seen[y] === 1) continue
        if (!implied(y, depth + 1)) { ok = false; break }
      }
    }
    redundant[v] = ok ? 1 : -1
    touched.push(v)
    return ok
  }
  const removable = (L: number): boolean => {
    const v = L >> 1, r = reason[v]!
    if (r < 0) return false
    const s = start[r]!
    for (let k = s; k < s + size[r]!; k++) {
      const y = arena[k]! >> 1
      if (y === v || level[y] === 0 || seen[y] === 1) continue
      if (!implied(y, 0)) return false
    }
    return true
  }

  for (;;) {
    const ci = propagate()
    if (nLevels === 0) { if (ci >= 0) return refute(ci); fix() }
    if (ci >= 0) {
      if (++conflicts > limit) return {kind: 'unknown', conflicts}
      sinceRestart++
      // First UIP: resolve the conflict back along the trail until one literal of the current level is left.
      let n = 1, open = 0, idx = trailLen - 1, lit = -1, c = ci
      for (;;) {
        const s = start[c]!
        for (let k = s; k < s + size[c]!; k++) {
          const q = arena[k]!, v = q >> 1
          if (q === lit || seen[v] || level[v] === 0) continue
          seen[v] = 1
          bumpVar(v)
          if (level[v] === nLevels) open++
          else learned[n++] = q
        }
        while (!seen[trail[idx]! >> 1]) idx--
        lit = trail[idx--]!
        seen[lit >> 1] = 0
        if (--open === 0) break
        c = reason[lit >> 1]!
      }
      learned[0] = lit ^ 1
      // seen marks the clause's literals below the current level (the current level's were cleared on the way); they
      // are unmarked once minimization, which reads them, is done.
      for (let t = 1; t < n; t++) inClause.push(learned[t]! >> 1)
      if (minimize) {
        let m = 1
        for (let t = 1; t < n; t++) if (!removable(learned[t]!)) learned[m++] = learned[t]!
        for (const v of touched) redundant[v] = 0
        touched.length = 0
        n = m
      }
      for (const v of inClause) seen[v] = 0
      inClause.length = 0
      bump /= decay
      // Back to the second-highest level in the clause, with that literal watched second.
      let back = 0, at = 1
      for (let t = 1; t < n; t++) { const lv = level[learned[t]! >> 1]!; if (lv > back) (back = lv, at = t) }
      if (n > 1) { const x = learned[1]!; learned[1] = learned[at]!; learned[at] = x }
      const cl: number[] = new Array(n)
      for (let t = 0; t < n; t++) cl[t] = dimacs(learned[t]!)
      if (drup) proof.push(cl)
      const id = lemma(cl, hintsFor(learned, n, ci))
      // LBD, before backjumping.
      stamp++
      let lbdValue = 0
      for (let t = 0; t < n; t++) { const lv = level[learned[t]! >> 1]!; if (levelStamp[lv] !== stamp) (levelStamp[lv] = stamp, lbdValue++) }
      backjump(back)
      if (n === 1) (assign(learned[0]!, -1), unitId[learned[0]! >> 1] = id)
      else {
        const nc = addClause(learned, n, id)
        clbd[nc] = lbdValue
        learnts.push(nc)
        attach(nc)
        assign(learned[0]!, nc)
      }
      emaFast += (lbdValue - emaFast) / 32
      emaSlow += (lbdValue - emaSlow) / 16384
      // Every so often, half the learned clauses go, those spanning the most levels first; never one that is the
      // reason for a current assignment, nor one spanning two levels or fewer.
      if (reduce && conflicts >= nextReduce) {
        nextReduce = conflicts + reduceBase + reduceInc * ++reductions
        const locked = (ci: number) => { const s = start[ci]!; for (const L of [arena[s]!, arena[s + 1]!]) if (lval[L] === 1 && reason[L >> 1] === ci) return true; return false }
        const order = learnts.filter(ci => !deleted[ci]).sort((a, b) => clbd[b]! - clbd[a]! || size[b]! - size[a]!)
        const gone: number[] = []
        for (const ci of order.slice(0, order.length >> 1)) if (clbd[ci]! > 2 && !locked(ci)) (deleted[ci] = 1, drup && proof.push({d: clauseDimacs(ci)}), gone.push(cid[ci]!))
        if (gone.length) {
          lrat.push({del: gone})
          // Drop the deleted clauses from every watch list.
          for (let L = 2; L < nLits; L++) {
            const d = wdata[L]!, m = wlen[L]!
            let j = 0
            for (let i = 0; i < m; i += 2) if (!deleted[d[i]! >> 1]) (d[j++] = d[i]!, d[j++] = d[i + 1]!)
            wlen[L] = j
          }
        }
        learnts.splice(0, learnts.length, ...learnts.filter(ci => !deleted[ci]))
      }
      const restart = restartPolicy === 'luby' ? conflicts >= nextRestart : sinceRestart >= 50 && emaFast > emaMargin * emaSlow
      if (restart) (backjump(0), nextRestart = conflicts + lubyUnit * luby(++restarts + 1), sinceRestart = 0)
      continue
    }
    // Decide: the unassigned variable of highest activity, at its saved phase.
    let best = 0
    while (hsize > 0) { const v = popMax(); if (lval[2 * v] === 0) { best = v; break } }
    if (best === 0) { const model: boolean[] = new Array(vars + 1).fill(false); for (let v = 1; v <= vars; v++) model[v] = lval[2 * v] === 1; return {kind: 'sat', model} }
    limits[nLevels++] = trailLen
    assign(2 * best + phase[best]!, -1)
  }
}

