// The trusted LRAT checker. Input clause i (from 0) has id i + 1. A lemma {id, clause, hints} follows when, with each of
// its literals assumed false, its hints taken in order are each unit (exactly one literal unassigned, none true: assign
// it true) until one is falsified (every literal false). No search: the hints are the propagation, so each check costs
// the hint clauses' lengths. A lemma with a literal and its negation is a tautology and needs no hints. A deletion
// {del: ids} removes clauses from what later hints may name. The proof refutes the input when it derives the empty
// clause. Lemma ids increase, so an id is never reused and a hint names one clause for good.
export type Clause = number[]
export type LratStep = {id: number, clause: Clause, hints: number[]} | {del: number[]}

export function checkLrat(vars: number, input: Clause[], steps: LratStep[]): boolean {
  const db = new Map<number, Clause>(input.map((c, i) => [i + 1, c]))
  const ok = (l: number) => Number.isInteger(l) && l !== 0 && Math.abs(l) <= vars
  if (!input.every(c => c.every(ok))) return false
  const val = new Int8Array(vars + 1) // 1 true, −1 false, 0 unassigned; reset after each lemma
  const set: number[] = []
  let last = input.length
  const assign = (lit: number) => (val[Math.abs(lit)] = lit > 0 ? 1 : -1, set.push(Math.abs(lit)))
  const value = (lit: number) => (lit > 0 ? val[lit]! : -val[-lit]!)
  const follows = (clause: Clause, hints: number[]): boolean => {
    for (const l of clause) {
      if (value(l) === 1) return true // l and −l both in the clause
      if (value(l) === 0) assign(-l)
    }
    for (const h of hints) {
      const c = db.get(h)
      if (!c) return false
      let open = 0
      for (const l of c) {
        const v = value(l)
        if (v === 1) return false // a satisfied hint is not unit
        if (v === 0 && open !== l) { if (open !== 0) return false; open = l } // a second unassigned literal
      }
      if (open === 0) return true // falsified: the conflict
      assign(open)
    }
    return false // the hints ran out without a conflict
  }
  for (const s of steps) {
    if ('del' in s) { for (const id of s.del) db.delete(id); continue }
    if (!Number.isInteger(s.id) || s.id <= last || !s.clause.every(ok)) return false
    last = s.id
    const good = follows(s.clause, s.hints)
    for (const x of set) val[x] = 0
    set.length = 0
    if (!good) return false
    if (s.clause.length === 0) return true
    db.set(s.id, s.clause)
  }
  return false
}
