// Untrusted model queries for a sequence of growing goals (e.g. counted MBQI).
// Preserve the CDCL state only while every old hypothesis is present verbatim.
// Removing/changing a hypothesis or taking the wide path starts afresh. A returned
// core is in the CURRENT goal's indices, never the session's insertion order.
import type {Goal, Path} from './kernel.ts'
import {type Refuted, cdclSession, growCdcl} from './cdcl.ts'
import {wideFor} from './prove.ts'

export function modelSequence(path: Path = new Map()): (goal: Goal, end: number) => Refuted {
  const fixedPath = new Map(path)
  let session: ReturnType<typeof cdclSession> | undefined, held: Goal | undefined, texts: string[] = []
  return (goal, end) => {
    const budget = {nodes: 0, until: end}
    if (wideFor(goal)) { session = undefined; held = undefined; return growCdcl(goal, fixedPath, budget, {model: true, core: true, point: true}) as Refuted }
    const current = goal.hyps.map(h => JSON.stringify(h)), at = new Map(current.map((h, i) => [h, i]))
    if (!held || !session || texts.some(h => !at.has(h))) {
      held = {name: goal.name, hyps: [...goal.hyps]}; texts = [...current]
      session = cdclSession(held, fixedPath, {model: true, core: true, point: true})
    } else {
      const old = new Set(texts)
      current.forEach((h, i) => { if (!old.has(h)) { held!.hyps.push(goal.hyps[i]!); texts.push(h); old.add(h) } })
      // Keep the conclusion last for the search's relevance heuristic.
      if (texts.at(-1) !== current.at(-1)) { held.hyps.push(goal.hyps.at(-1)!); texts.push(current.at(-1)!) }
    }
    const out = session.run(budget) as Refuted
    return out.core ? {...out, core: [...new Set(out.core.map(i => at.get(texts[i]!)!))]} : out
  }
}
