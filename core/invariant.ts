// Strengthening a law that holds but isn't inductive (Houdini): candidate invariants from templates over the machine's
// own variables and constants, those false at the start dropped, then any candidate that one step can break (assuming
// all the others) dropped, until the rest are inductive together. If the law follows from them, it is proven.
// Templates, for state variables u, w, params y, and constants c, a from the machine:
//   u <= c        u <= y + c        u + a·w <= y + c        u + a·w <= c
import {type C, type E, type Law, type Machine, atMost, n, plus, prove, times, x} from './machine.ts'
import {checkRefutation} from './check.ts'
import {negate, solve} from './solver.ts'

function constantsOf(m: Machine): number[] {
  const out = new Set<number>()
  const inE = (e: E): void => {
    if (e.op === 'const') out.add(e.value)
    else if (e.op === 'mul') (out.add(e.k), inE(e.a))
    else if (e.op === 'if') (inC(e.c), inE(e.then), inE(e.else))
    else if (e.op === 'get') inE(e.key)
    else if ('a' in e) (inE(e.a), inE(e.b))
  }
  const inC = (c: C): void => (c.op === 'flag' || c.op === 'all' ? undefined : c.op === 'not' ? inC(c.x) : c.op === 'and' || c.op === 'or' ? c.xs.forEach(inC) : (inE(c.a), inE(c.b)))
  Object.values(m.step.state ?? {}).forEach(inE)
  return [...out].filter(c => c > 0)
}

export function candidates(m: Machine): Law[] {
  const cs = constantsOf(m)
  const offsets = [...new Set([0, ...cs, ...cs.flatMap(a => cs.map(b => a * b))])].sort((a, b) => a - b)
  const state = Object.keys(m.state)
  const out: Law[] = []
  const law = (name: string, holds: C) => out.push({name, holds})
  for (const u of state) {
    for (const c of offsets) law(`${u} <= ${c}`, atMost(x(u), n(c)))
    for (const y of m.params) for (const c of offsets) law(`${u} <= ${y} + ${c}`, atMost(x(u), plus(x(y), n(c))))
    for (const w of state.filter(w => w !== u)) for (const a of cs) for (const c of offsets) {
      law(`${u} + ${a}${w} <= ${c}`, atMost(plus(x(u), times(a, x(w))), n(c)))
      for (const y of m.params) law(`${u} + ${a}${w} <= ${y} + ${c}`, atMost(plus(x(u), times(a, x(w))), plus(x(y), n(c))))
    }
  }
  return out
}

export function strengthen(m: Machine, goal: Law) {
  let kept = candidates(m).filter(c => prove(m, c, [c]).obligations.filter(o => o.phase === 'start').every(o => o.verdict.kind === 'refuted'))
  const started = kept.length
  for (let changed = true; changed;) {
    changed = false
    for (const c of [...kept]) {
      const stepOk = prove(m, c, kept).obligations.filter(o => o.phase === 'step').every(o => o.verdict.kind === 'refuted')
      if (!stepOk) {
        kept = kept.filter(k => k !== c)
        changed = true
      }
    }
  }
  // Keep only what the goal needs: drop an invariant whenever the goal and the rest stay inductive together.
  const inductive = (set: Law[]) => [goal, ...set].every(law => prove(m, law, [goal, ...set]).proven)
  if (!inductive(kept)) return {candidates: candidates(m).length, trueAtStart: started, invariants: kept, proven: false}
  for (const c of [...kept].reverse()) {
    const without = kept.filter(k => k !== c)
    if (inductive(without)) kept = without
  }
  void negate, solve, checkRefutation
  return {candidates: candidates(m).length, trueAtStart: started, invariants: kept, proven: true}
}
