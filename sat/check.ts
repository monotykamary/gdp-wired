// The trusted part. A model satisfies a CNF when every clause has a true literal. A DRUP proof refutes it when every
// proof clause is a reverse-unit-propagation consequence of the input and the proof clauses before it (assume each of
// its literals false, propagate units, reach a clause with every literal false), and the last proof clause is empty.
// Propagation watches two literals per clause: a clause is only looked at when one of its watched literals turns false,
// and a literal is assigned only when every other literal of its clause is false. Each check starts from nothing.
//
// Backward (the default): check the empty clause first with every clause available, mark the clauses its conflict
// used (following each propagated literal to the clause that forced it), then go through the proof in reverse: drop
// each lemma, and check it against what comes before it only if something checked later used it. The marked lemmas
// form a proof on their own, each checked against earlier clauses, so the unmarked ones need no check. Forward checks
// every lemma in order. A deletion {d: clause} removes one copy of that clause from what later lemmas may use (going
// backward, it comes back); deleting only ever makes a check harder.
export type Clause = number[]
export type Step = Clause | {d: Clause}

export const checkModel = (clauses: Clause[], model: boolean[]): boolean =>
  clauses.every(c => c.some(l => (l > 0 ? model[l] === true : model[-l] === false)))

export function checkProof(clauses: Clause[], proof: Step[], mode: 'backward' | 'forward' = 'backward', stats = {checked: 0}): boolean {
  const last = proof.at(-1)
  if (!Array.isArray(last) || last.length !== 0) return false
  const steps = proof.slice(0, -1)
  const lemmas = steps.filter(s => Array.isArray(s))
  const all = [...clauses, ...lemmas].map(c => [...new Set(c)]) // a repeated literal would count twice
  // Each step as a clause id: an added lemma's own, a deletion's the latest copy of that clause still there (or −1).
  const copies = new Map<string, number[]>(), key = (c: Clause) => [...new Set(c)].sort((a, b) => a - b).join(' ')
  let next = clauses.length
  for (const [id, c] of clauses.entries()) copies.get(key(c))?.push(id) ?? copies.set(key(c), [id])
  const ids = steps.map(s => {
    if (Array.isArray(s)) return (copies.get(key(s))?.push(next) ?? copies.set(key(s), [next]), next++)
    return copies.get(key(s.d))?.pop() ?? -1
  })
  const vars = all.reduce((most, c) => c.reduce((m, l) => Math.max(m, Math.abs(l)), most), 0)
  const val = new Int8Array(vars + 1) // 1 true, −1 false, 0 unassigned
  const reason = new Int32Array(vars + 1).fill(-1) // the clause that forced a variable, −1 for an assumption
  const value = (l: number) => (l > 0 ? val[l]! : -val[-l]!)
  const active = all.map((_, id) => id < clauses.length) // ids: the input, then the lemmas
  const used = all.map(() => false), gone = all.map(() => false)
  const watches: number[][] = Array.from({length: 2 * vars + 2}, () => [])
  const watching = (l: number) => watches[l > 0 ? 2 * l : -2 * l + 1]!
  const units: number[] = [], empties: number[] = []
  for (const [id, c] of all.entries()) {
    if (c.length === 0) empties.push(id)
    else if (c.length === 1) units.push(id)
    else (watching(c[0]!).push(id), watching(c[1]!).push(id))
  }

  // Assumes `lits` true, with the active unit clauses, and propagates over the active clauses. On a conflict, marks
  // the conflicting clause and every clause that forced one of its literals, transitively, and returns true.
  const conflicts = (lits: number[]): boolean => {
    stats.checked++
    const trail: number[] = []
    let conflict: number[] | undefined // false literals that together contradict
    const set = (l: number, why: number) => (val[Math.abs(l)] = l > 0 ? 1 : -1, reason[Math.abs(l)] = why, trail.push(l))
    const empty = empties.find(id => active[id])
    if (empty !== undefined) (used[empty] = true, conflict = [])
    for (const l of lits) if (!conflict) value(l) === -1 ? (conflict = [l]) : value(l) === 0 && set(l, -1)
    for (const id of units) if (!conflict && active[id]) {
      const l = all[id]![0]!
      if (value(l) === -1) (used[id] = true, conflict = [l])
      else if (value(l) === 0) set(l, id)
    }
    // The clauses watching f, now false: those already used (core) or the others, in two passes.
    const visit = (f: number, core: boolean) => {
      const list = watching(f)
      let keep = 0
      for (let i = 0; i < list.length; i++) {
        const id = list[i]!, c = all[id]!
        if (gone[id]) continue // a lemma behind the backward check: never used again
        if (!active[id] || used[id] !== core) { list[keep++] = id; continue }
        if (c[0] === f) (c[0] = c[1]!, c[1] = f)
        let other = -1
        if (value(c[0]!) !== 1) for (let t = 2; t < c.length; t++) if (value(c[t]!) !== -1) { other = t; break }
        if (other >= 0) { // watch a literal that isn't false instead
          (c[1] = c[other]!, c[other] = f)
          watching(c[1]!).push(id)
          continue
        }
        list[keep++] = id
        if (value(c[0]!) === 1) continue
        if (value(c[0]!) === -1) { used[id] = true; conflict = c; while (++i < list.length) list[keep++] = list[i]!; break }
        set(c[0]!, id) // every other literal is false: c[0] is forced
      }
      list.length = keep
    }
    // Core first: propagate with the used clauses as far as they go before one step with the rest, so conflicts are
    // found with clauses already marked and fewer new lemmas need checking. Each pass sees every false literal.
    for (let core = 0, rest = 0; !conflict;) {
      if (core < trail.length) visit(-trail[core++]!, true)
      else if (rest < trail.length) visit(-trail[rest++]!, false)
      else break
    }
    if (conflict) { // mark the reasons, back from the conflict
      const seen = new Set<number>(), stack = conflict.map(Math.abs)
      while (stack.length) {
        const x = stack.pop()!
        if (seen.has(x) || reason[x]! < 0) continue
        seen.add(x)
        used[reason[x]!] = true
        stack.push(...all[reason[x]!]!.map(Math.abs))
      }
    }
    for (const l of trail) (val[Math.abs(l)] = 0, reason[Math.abs(l)] = -1)
    return conflict !== undefined
  }

  if (mode === 'forward') {
    for (const [i, s] of steps.entries()) {
      if (ids[i]! < 0) continue
      if (Array.isArray(s) && !conflicts(all[ids[i]!]!.map(l => -l))) return false
      active[ids[i]!] = Array.isArray(s)
    }
    return conflicts([])
  }
  for (const [i, s] of steps.entries()) if (ids[i]! >= 0) active[ids[i]!] = Array.isArray(s)
  if (!conflicts([])) return false
  for (let i = steps.length - 1; i >= 0; i--) {
    const id = ids[i]!
    if (id < 0) continue
    if (!Array.isArray(steps[i])) { active[id] = true; continue }
    active[id] = false
    gone[id] = true
    if (used[id] && !conflicts(all[id]!.map(l => -l))) return false
  }
  return true
}
