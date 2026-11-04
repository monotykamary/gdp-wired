// The e-graph returns candidates only. The existing kernel constructs and checks every goal.
import {type CNode, type Cyclic, type Fact, type Use, mainGoal, premiseGoal, descentGoal, refuseCyclic} from '../../kernel/cyclic.ts'
import {type Goal, type Tree, type Path, canon, linear} from '../../kernel/kernel.ts'
import type {E} from '../../core/machine.ts'
import {scale, sub} from '../../core/solver.ts'
import {fullWork, grow, withWall, withWork} from '../../kernel/prove.ts'
import {Exhausted, Meter} from './match.ts'
export type Spec = Omit<CNode, 'main' | 'uses'> & {uses: Omit<Use, 'premises' | 'descent'>[]}
export type Result = {checked: boolean, reason?: string, proof?: Cyclic, proofUnits: number, hintUnits: number, ms: number}
export function certify(facts: Fact[], specs: Spec[], matchingUnits = 0, totalUnits = 2_000_000, prefix: CNode[] = [], hints: [E, E][] = []): Result {
  const start = performance.now(), work = fullWork(), hintMeter = new Meter(4096, start + 5000)
  try {
    if (!Number.isSafeInteger(totalUnits) || totalUnits < 0 || !Number.isSafeInteger(matchingUnits) || matchingUnits < 0) throw new Error('invalid combined budget')
    if (matchingUnits >= totalUnits) throw new Exhausted('combined work budget')
    if (hints.length > 4) throw new Exhausted('split hint limit')
    const splits = hints.flatMap(([a, b]) => {
      hintMeter.tick()
      const lhs = linear(a, new Map()), rhs = linear(b, new Map())
      if (!lhs || !rhs) throw new Error('nonlinear split hint')
      const d = sub(lhs, rhs)
      return [d, scale(d, -1)]
    })
    const proof = withWall(start + 5000, () => withWork(work + totalUnits - matchingUnits, () => {
      const tree = (goal: Goal): Tree => {
        const visit = (at: number, path: Path): Tree => {
          hintMeter.tick()
          if (matchingUnits + hintMeter.used >= totalUnits) throw new Exhausted('combined work budget')
          const split = splits[at]
          if (split) {
            const key = canon(split)
            if (path.has(key) || Object.keys(split).every(k => k === '1')) return visit(at + 1, path)
            return {split, yes: visit(at + 1, new Map(path).set(key, {lin: split, holds: true})),
              no: visit(at + 1, new Map(path).set(key, {lin: split, holds: false}))}
          }
          const out = withWork(work + totalUnits - matchingUnits - hintMeter.used, () => grow(goal, path))
          if (!('tree' in out)) throw new Error(`${goal.name}: ${out.stuck}`)
          return out.tree
        }
        return visit(0, new Map())
      }
      if (prefix.length > specs.length) throw new Error('invalid certificate prefix')
      // Reuse lemma trees, not a trusted verdict. The complete graph is checked below.
      return {facts, nodes: [...prefix, ...specs.slice(prefix.length).map(n => ({...n, main: tree(mainGoal(facts, specs, n)), uses: n.uses.map(u => {
        const target = specs[u.node]
        if (!target) throw new Error('missing lemma')
        return {...u, premises: target.hyps.map((c, i) => tree(premiseGoal(facts, n, u, c, i))), descent: tree(descentGoal(facts, n, u, target))}
      })}))]}
    }))
    const reason = refuseCyclic(proof)
    return {checked: reason === undefined, reason, proof, proofUnits: fullWork() - work, hintUnits: hintMeter.used, ms: performance.now() - start}
  } catch (error) {
    return {checked: false, reason: String(error), proofUnits: fullWork() - work, hintUnits: hintMeter.used, ms: performance.now() - start}
  }
}
