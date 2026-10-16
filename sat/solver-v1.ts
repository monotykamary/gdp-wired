// CDCL: two watched literals, first-UIP learning with recursive minimization, VSIDS-style activity with phase saving,
// Luby restarts, and periodic deletion of learned clauses with many decision levels (LBD). Clauses are arrays of
// nonzero integers (DIMACS literals). Every answer carries evidence check.ts verifies:
//   sat      a model (model[v] for v = 1..vars)
//   unsat    a DRUP proof: the learned clauses in the order learned, deletions as {d: clause}, then the empty clause;
//            each learned clause follows by unit propagation alone from the clauses not yet deleted before it
//            and the same refutation as LRAT (lrat.ts): input clause i has id i + 1; each lemma gets the next id and
//            names its hints, the clauses that, in order, become unit and then falsified once its literals are false;
//            literals fixed at level 0 become unit lemmas of their own, so later hints name one clause for each
//   unknown  the conflict budget ran out
export type Clause = number[]
export type Step = Clause | {d: Clause}
export type LratStep = {id: number, clause: Clause, hints: number[]} | {del: number[]}
export type Result = {kind: 'sat', model: boolean[]} | {kind: 'unsat', proof: Step[], lrat: LratStep[]} | {kind: 'unknown', conflicts: number}
export type Options = {limit?: number, minimize?: boolean, reduce?: boolean}

// Only the lemmas the empty clause depends on, through hints, and deletions of those: a smaller proof of the same thing.
const trim = (lrat: LratStep[]): LratStep[] => {
  const used = new Set<number>([(lrat.at(-1) as {id: number}).id])
  for (let i = lrat.length - 1; i >= 0; i--) { const s = lrat[i]!; if ('id' in s && used.has(s.id)) for (const h of s.hints) used.add(h) }
  return lrat.flatMap(s => ('id' in s ? (used.has(s.id) ? [s] : []) : (s.del.some(id => used.has(id)) ? [{del: s.del.filter(id => used.has(id))}] : [])))
}

const luby = (i: number): number => {
  let k = 1
  while ((1 << k) - 1 < i) k++
  return (1 << k) - 1 === i ? 1 << (k - 1) : luby(i - (1 << (k - 1)) + 1)
}

export function solve(vars: number, input: Clause[], {limit = Infinity, minimize = true, reduce = true}: Options = {}): Result {
  const proof: Step[] = [], lrat: LratStep[] = []
  let nextId = input.length + 1
  const lemma = (clause: Clause, hints: number[]) => (lrat.push({id: nextId, clause, hints}), nextId++)
  const val = new Int8Array(vars + 1) // 1 true, -1 false, 0 unassigned
  const level = new Int32Array(vars + 1), reason = new Int32Array(vars + 1).fill(-1)
  const activity = new Float64Array(vars + 1), phase = new Int8Array(vars + 1).fill(-1)
  const seen = new Uint8Array(vars + 1), redundant = new Int8Array(vars + 1) // 1 implied by the clause, −1 not, 0 unknown
  const learnts: number[] = [], lbd: number[] = [], deleted: boolean[] = []
  const clauses: Clause[] = [], ids: number[] = [] // clause index → LRAT id
  const unitId = new Int32Array(vars + 1), pos = new Int32Array(vars + 1), mark = new Int32Array(vars + 1)
  let stamp = 0, fixed = 0
  const watches: number[][] = Array.from({length: 2 * vars + 2}, () => [])
  const w = (lit: number) => (lit > 0 ? 2 * lit : -2 * lit + 1)
  const value = (lit: number) => (lit > 0 ? val[lit]! : -val[-lit]!)
  const trail: number[] = [], limits: number[] = []
  let head = 0, bump = 1

  const assign = (lit: number, why: number) => {
    const x = Math.abs(lit)
    val[x] = lit > 0 ? 1 : -1
    level[x] = limits.length
    reason[x] = why
    pos[x] = trail.length
    trail.push(lit)
  }
  // Watches the first two literals; a unit clause is assigned (or conflicts) at once.
  const attach = (c: Clause, id: number): number => {
    const i = clauses.push(c) - 1
    ids[i] = id
    if (c.length >= 2) (watches[w(c[0]!)]!.push(i), watches[w(c[1]!)]!.push(i))
    return i
  }
  // Propagates the trail; returns a conflicting clause's index, or −1.
  const propagate = (): number => {
    while (head < trail.length) {
      const falsified = -trail[head++]!
      const list = watches[w(falsified)]!
      let keep = 0
      for (let j = 0; j < list.length; j++) {
        const ci = list[j]!, c = clauses[ci]!
        if (deleted[ci]) continue
        if (c[0] === falsified) (c[0] = c[1]!, c[1] = falsified)
        if (value(c[0]!) === 1) { list[keep++] = ci; continue }
        let moved = false
        for (let t = 2; t < c.length; t++) if (value(c[t]!) !== -1) {
          c[1] = c[t]!; c[t] = falsified
          watches[w(c[1]!)]!.push(ci)
          moved = true
          break
        }
        if (moved) continue
        list[keep++] = ci
        if (value(c[0]!) === -1) {
          while (++j < list.length) list[keep++] = list[j]!
          list.length = keep
          return ci
        }
        assign(c[0]!, ci)
      }
      list.length = keep
    }
    return -1
  }
  const backjump = (to: number) => {
    while (limits.length > to) {
      const start = limits.pop()!
      while (trail.length > start) {
        const x = Math.abs(trail.pop()!)
        phase[x] = val[x]!
        val[x] = 0
        reason[x] = -1
      }
    }
    head = trail.length
  }
  const unsat = (hints: number[]) => (proof.push([]), lemma([], hints), {kind: 'unsat' as const, proof, lrat: trim(lrat)})
  // Level 0: each literal propagated there becomes a unit lemma (the units of its reason's other literals, then the
  // reason), so a hint about it is one clause.
  const fix = () => {
    for (; fixed < trail.length; fixed++) {
      const lit = trail[fixed]!, x = Math.abs(lit)
      if (unitId[x] !== 0) continue
      const r = clauses[reason[x]!]!
      unitId[x] = lemma([lit], [...r.filter(q => q !== lit).map(q => unitId[Math.abs(q)]!), ids[reason[x]!]!])
    }
  }
  // A conflict at level 0: every literal of the clause is fixed false.
  const refute = (ci: number) => (fix(), unsat([...clauses[ci]!.map(q => unitId[Math.abs(q)]!), ids[ci]!]))
  // A learned clause's hints: the clauses its conflict used (the conflicting clause, and the reason of every literal
  // reached from it that isn't in the learned clause), level-0 units first, then reasons in trail order, the conflicting
  // clause last; with the learned clause's literals false, each reason is unit in turn and the last is falsified.
  const hintsFor = (learned: Clause, ci: number): number[] => {
    stamp++
    for (const q of learned) mark[Math.abs(q)] = stamp
    const units: number[] = [], reached: number[] = [], stack = [ci]
    while (stack.length) for (const q of clauses[stack.pop()!]!) {
      const x = Math.abs(q)
      if (mark[x] === stamp) continue
      mark[x] = stamp
      if (level[x] === 0) units.push(unitId[x]!)
      else if (reason[x]! < 0) throw new Error('a decision outside the learned clause')
      else (reached.push(x), stack.push(reason[x]!))
    }
    reached.sort((a, b) => pos[a]! - pos[b]!)
    return [...units, ...reached.map(x => ids[reason[x]!]!), ids[ci]!]
  }

  for (const [i, raw] of input.entries()) {
    const c = [...new Set(raw)]
    if (c.some(l => c.includes(-l))) continue
    if (c.length === 0) return unsat([i + 1])
    if (c.length === 1) {
      const x = Math.abs(c[0]!)
      if (value(c[0]!) === -1) return unsat([unitId[x]!, i + 1])
      if (value(c[0]!) === 0) (assign(c[0]!, -1), unitId[x] = i + 1)
    } else attach(c, i + 1)
  }
  { const ci = propagate(); if (ci >= 0) return refute(ci) }
  fix()

  let conflicts = 0, restarts = 0, nextRestart = 100 * luby(1), reductions = 0, nextReduce = 2000
  for (;;) {
    const ci = propagate()
    if (limits.length === 0) { if (ci >= 0) return refute(ci); fix() }
    if (ci >= 0) {
      if (++conflicts > limit) return {kind: 'unknown', conflicts}
      // First UIP: resolve the conflict back along the trail until one literal of the current level is left.
      const learned: number[] = [0]
      let open = 0, idx = trail.length - 1, lit = 0, c = clauses[ci]!
      for (;;) {
        for (const q of c) {
          const x = Math.abs(q)
          if (q === lit || seen[x] || level[x] === 0) continue
          seen[x] = 1
          activity[x] += bump
          if (activity[x]! > 1e100) { for (let y = 1; y <= vars; y++) activity[y]! *= 1e-100; bump *= 1e-100 }
          if (level[x] === limits.length) open++
          else learned.push(q)
        }
        while (!seen[Math.abs(trail[idx]!)]) idx--
        lit = trail[idx--]!
        seen[Math.abs(lit)] = 0
        if (--open === 0) break
        c = clauses[reason[Math.abs(lit)]!]!
      }
      learned[0] = -lit
      // Minimization: drop a literal whose reason's other literals are, recursively, in the clause or at level 0.
      const implied = (x: number, depth: number): boolean => {
        if (redundant[x] !== 0) return redundant[x] === 1
        const r = reason[x]!
        const ok = r >= 0 && depth < 64 && clauses[r]!.every(p => {
          const y = Math.abs(p)
          return y === x || level[y] === 0 || seen[y] === 1 || implied(y, depth + 1)
        })
        redundant[x] = ok ? 1 : -1
        touched.push(x)
        return ok
      }
      const touched: number[] = []
      const kept = minimize ? [learned[0]!, ...learned.slice(1).filter(q => reason[Math.abs(q)]! < 0 || !clauses[reason[Math.abs(q)]!]!.every(p => {
        const y = Math.abs(p)
        return y === Math.abs(q) || level[y] === 0 || seen[y] === 1 || implied(y, 0)
      }))] : learned
      for (const x of touched) redundant[x] = 0
      for (const q of learned) seen[Math.abs(q)] = 0
      if (kept !== learned) learned.splice(0, learned.length, ...kept)
      bump /= 0.95
      // Back to the second-highest level in the clause, with that literal watched second.
      let back = 0, at = 1
      for (let t = 1; t < learned.length; t++) if (level[Math.abs(learned[t]!)]! > back) (back = level[Math.abs(learned[t]!)]!, at = t)
      if (learned.length > 1) [learned[1], learned[at]] = [learned[at]!, learned[1]!]
      proof.push([...learned])
      const id = lemma([...learned], hintsFor(learned, ci))
      backjump(back)
      if (learned.length === 1) (assign(learned[0]!, -1), unitId[Math.abs(learned[0]!)] = id)
      else {
        const ci = attach(learned, id)
        learnts.push(ci)
        lbd[ci] = new Set(learned.map(q => level[Math.abs(q)])).size
        assign(learned[0]!, ci)
      }
      // Every so often, half the learned clauses go, those spanning the most levels first; never one that is the
      // reason for a current assignment, nor one spanning two levels or fewer.
      if (reduce && conflicts >= nextReduce) {
        nextReduce = conflicts + 2000 + 300 * ++reductions
        const locked = (ci: number) => reason[Math.abs(clauses[ci]![0]!)] === ci && value(clauses[ci]![0]!) === 1
        const order = learnts.filter(ci => !deleted[ci]).sort((a, b) => lbd[b]! - lbd[a]! || clauses[b]!.length - clauses[a]!.length)
        const gone: number[] = []
        for (const ci of order.slice(0, order.length >> 1)) if (lbd[ci]! > 2 && !locked(ci)) (deleted[ci] = true, proof.push({d: [...clauses[ci]!]}), gone.push(ids[ci]!))
        if (gone.length) lrat.push({del: gone})
        learnts.splice(0, learnts.length, ...learnts.filter(ci => !deleted[ci]))
      }
      if (conflicts >= nextRestart) (backjump(0), nextRestart = conflicts + 100 * luby(++restarts + 1))
      continue
    }
    // Decide: the unassigned variable of highest activity, at its saved phase.
    let best = 0
    for (let x = 1; x <= vars; x++) if (val[x] === 0 && (best === 0 || activity[x]! > activity[best]!)) best = x
    if (best === 0) return {kind: 'sat', model: Array.from(val, y => y === 1)}
    limits.push(trail.length)
    assign(phase[best] === 1 ? best : -best, -1)
  }
}
