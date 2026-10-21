// Houdini over the rule a CHC system builds, with proveRule as its judge: candidate laws per predicate (each an
// implication from being at that predicate), those false in a state a run reached dropped, then rounds of proveRule
// over the rest; each round's counterexample drops the candidate it names and every candidate its step breaks, until
// the rest are inductive together. The answer is proveRule on the law and the candidates kept: a checked proof or none.
// Templates, at predicate p, over its Int arguments u, w, its Bool arguments a, and constants c from the system:
//   not at p        u ≥ c        u ≤ c        u ≤ w + d        u ≥ w + d (d ∈ −1, 0, 1)        u + w ≥ c        a        ¬a
import {type Law, type State, evalC, interpret} from '../../core/machine.ts'
import {type Choice, type Cond, type Int, proveRule} from '../../core/dsl.ts'
import type {Chc, Sx} from './chc.ts'
import type {Built} from './translate.ts'

const numerals = (s: Sx, out: Set<number>) => {
  if (typeof s === 'string') { if (/^\d+$/.test(s) && Number.isSafeInteger(Number(s))) out.add(Number(s)) } else s.forEach(x => numerals(x, out))
}

export function candidates(b: Built, chc: Chc, maxConsts = 12): Law[] {
  const found = new Set<number>([0, 1])
  for (const c of chc.clauses) [...c.constraint, ...c.body.flatMap(a => a.args), ...(c.head?.args ?? [])].forEach(s => numerals(s, found))
  const consts = [...new Set([...found].sort((x, y) => x - y).slice(0, maxConsts).flatMap(c => [c, -c]))]
  const out: Law[] = [], r = b.rule as unknown as {law: (name: string, f: (env: Record<string, unknown>) => Cond) => Law}
  b.predNames.forEach((pred, j) => {
    const p = b.loc[j]!, sorts = chc.preds.get(pred)!
    const ints = sorts.filter(s => s === 'Int').map((_, k) => `i${k}`), bools = sorts.filter(s => s === 'Bool').map((_, k) => `b${k}`)
    const at = (name: string, f: (env: Record<string, unknown>) => Cond) => out.push(r.law(`${pred}: ${name}`, env => (env.loc as Choice<string>).is(p).implies(f(env))))
    out.push(r.law(`${pred}: unreachable`, env => (env.loc as Choice<string>).is(p).not()))
    const I = (env: Record<string, unknown>, u: string) => env[u] as Int
    for (const u of ints) for (const c of consts) { at(`${u} >= ${c}`, e => I(e, u).atLeast(c)); at(`${u} <= ${c}`, e => I(e, u).atMost(c)) }
    for (const u of ints) for (const w of ints) if (u !== w) for (const d of [-1, 0, 1]) { at(`${u} <= ${w} + ${d}`, e => I(e, u).atMost(I(e, w).plus(d))); at(`${u} >= ${w} + ${d}`, e => I(e, u).atLeast(I(e, w).plus(d))) }
    for (const [k, u] of ints.entries()) for (const w of ints.slice(k + 1)) for (const c of consts) at(`${u} + ${w} >= ${c}`, e => I(e, u).plus(I(e, w)).atLeast(c))
    for (const a of bools) { at(a, e => e[a] as Cond); at(`not ${a}`, e => (e[a] as Cond).not()) }
  })
  return out
}

export function houdini(b: Built, chc: Chc, seen: State[], opts: {ms: number, maxCandidates?: number}) {
  const m = b.rule.machine, run = interpret(m), until = performance.now() + opts.ms
  const holds = (l: Law, st: State) => { try { return evalC(l.holds, {}, st, m) } catch { return false } }
  const all = candidates(b, chc), start = run.init({})
  let kept = all.filter(l => holds(l, start) && seen.every(st => holds(l, st)))
  const afterRuns = kept.length
  if (kept.length > (opts.maxCandidates ?? 2000)) return {candidates: all.length, afterRuns, kept: [] as Law[], rounds: 0, proven: false, why: 'too many candidates'}
  let rounds = 0, inductive = false
  while (performance.now() < until) {
    rounds++
    const v = proveRule(b.rule, kept)
    if (v.proven && v.checked) { inductive = true; break }
    if (!v.goal) break
    const name = v.goal.replace(/ @.*$/, ''), drop = new Set(kept.filter(l => l.name === name))
    if (v.witness) {
      const pre: State = {scalars: Object.fromEntries(Object.keys(m.state).map(n => [n, v.witness![n] ?? 0])), maps: {}}
      const input = Object.fromEntries(m.inputs.map(n => [n, v.witness![n] ?? 0]))
      try {
        const next = v.goal.endsWith('@start') ? start : run.step({}, pre, input)
        for (const l of kept) if (!holds(l, next)) drop.add(l)
      } catch { /* the witness isn't a state the interpreter takes: drop only the candidate named */ }
    }
    if (!drop.size) break
    kept = kept.filter(l => !drop.has(l))
  }
  if (!inductive) return {candidates: all.length, afterRuns, kept, rounds, proven: false, why: 'no inductive set in time'}
  const v = proveRule(b.rule, [b.law, ...kept])
  return {candidates: all.length, afterRuns, kept, rounds, proven: v.proven && v.checked}
}
