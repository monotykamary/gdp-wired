// Fast, ordinary checked closure when every target count is unchanged under
// the selected operation. No zero-phase law or count witness is assumed.
import {type Law, type Machine} from './machine.ts'
import {countsForReads} from './count-facts.ts'
import {countFrameConditions, fixedCountFrameCase, ownCountLawInstance, proveCountFrameGoal} from './count-frames.ts'
import {discoverCountGuardShape} from './count-guard-shape.ts'
import {type CountRequestBuilder, type CountStrategyProof, type CountStrategyOptions, finishCountStrategy} from './count-strategy.ts'
import {countedObligations, frameOk} from '../kernel/kernel.ts'
import {fullRate, fullWork, late, withDeadline} from '../kernel/prove.ts'
export function proveFixedCountFrame(m: Machine, family: Law[], law: Law, seed: Parameters<typeof ownCountLawInstance>[1], until: number, requestFor: CountRequestBuilder, options: CountStrategyOptions = {}): CountStrategyProof | undefined {
  return withDeadline(until, () => {
    if (late(until) || !family.includes(law)) return
    const choice = fixedCountFrameCase(m), shape = discoverCountGuardShape(m, law, family)
    if (!choice || !shape) return
    options.trace?.({query: 'frame-eligibility', outcome: 'start'})
    const start = fullWork()
    const instances = ownCountLawInstance(law, seed), step = countedObligations(m, family, {[law.name]: instances}, family.indexOf(law)).at(-1)!
    const request = requestFor(step.goal, step.decls), counts = countsForReads(step.decls, request.reads), targets = new Set([shape.voteMap, shape.rowMap]), when = countFrameConditions(choice)
    if (!counts) return
    const post = request.reads.filter(r => r[1].endsWith('#') && targets.has(r[1].slice(0, -1)))
    if (!post.length || post.some(([name, map, key]) => {
      const pre = request.reads.find(r => r[1] === map.slice(0, -1) && JSON.stringify(r[2]) === JSON.stringify(key))
      return !pre || !frameOk(counts, {post: name, pre: pre[0], when})
    })) return
    options.trace?.({query: 'frame-eligibility', outcome: 'eligible', units: (fullWork() - start) / fullRate})
    const cert = proveCountFrameGoal(step.goal, step.decls, request, choice, targets, until, undefined, {deferCheck: !!options.deferToComposition, trace: options.trace, minimalView: options.minimalView, leafUnits: options.leafUnits})
    return cert && finishCountStrategy(m, family, law, instances, shape.voteMap, cert, until, requestFor, undefined, options)
  })
}
