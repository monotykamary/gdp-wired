// Searches for step laws and k-step laws: the examples' own laws and broken variants, and the composition examples, each
// a machine and the law the kernel is asked to prove. A broken one must turn up a run that breaks its law (replayed by
// core/watch.ts); a proven one must turn up nothing within its space.
import type {Machine} from '../core/machine.ts'
import type {Watched} from '../core/watch.ts'
import type {StepLaw} from '../kernel/kernel.ts'
import type {Space} from './compile.ts'
import {domains} from '../examples/index.ts'
import {counterLaws, counterSteps, counters, meterRefinement} from '../examples/composition.ts'

const rule = (domain: string, name: string) => {
  const c = domains.find(d => d.domain === domain)!.cases.find(cc => cc.name === name)
  if (!c || c.kind !== 'rule') throw new Error(`no rule case ${domain} / ${name}`)
  return c
}
const stepLaw = (laws: StepLaw[] | undefined, name: string) => { const sl = laws?.find(l => l.name === name); if (!sl) throw new Error(`no step law ${name}`); return sl }
const variant = (domain: string, name: string, bug: string) => { const b = rule(domain, name).broken.find(bb => bb.name === bug); if (!b) throw new Error(`no variant ${bug}`); return b }

export type StepSearch = {what: string, m: Machine, law: Watched, space: Space, breaks: boolean}
const release = rule('operations', 'release lifecycle'), skips = variant('operations', 'release lifecycle', 'skips staging')
const auction = rule('commerce', 'auction'), reserveOnly = variant('commerce', 'auction', 'checks the reserve only')
const noClamp = meterRefinement('no clamp'), strict = meterRefinement('strict'), refines = meterRefinement()
const twoTurns = counterSteps[1]!

export const stepSearches: StepSearch[] = [
  // Two steps: a release that skips staging retires two steps after it is built (promote, then retire).
  {what: 'release, skips staging: two steps from built never retire', m: skips.rule.machine, law: stepLaw(skips.steps, 'two steps from built never retire'), space: {depth: 5, bound: 3}, breaks: true},
  {what: 'release: two steps from built never retire', m: release.rule.machine, law: stepLaw(release.steps, 'two steps from built never retire'), space: {depth: 6, bound: 3}, breaks: false},
  {what: 'release: the step after a rollback never retires', m: release.rule.machine, law: stepLaw(release.steps, 'the step after a rollback never retires'), space: {depth: 6, bound: 3}, breaks: false},
  // One step: comparing a bid with the reserve alone lets the high bid fall.
  {what: 'auction, reserve only: the high bid never falls', m: reserveOnly.rule.machine, law: stepLaw(reserveOnly.steps, 'the high bid never falls'), space: {depth: 3, bound: 3}, breaks: true},
  {what: 'auction: two refused bids change nothing', m: auction.rule.machine, law: stepLaw(auction.steps, 'two refused bids change nothing'), space: {depth: 3, bound: 3}, breaks: false},
  // Refinement: unclamped, the spec is sent a spend it doesn't allow (a step law); strict, the relation drifts (a law).
  {what: 'countdown, no clamp: the meter allows what it is sent', m: noClamp.machine, law: noClamp.stepLaws[0]!, space: {depth: 3, bound: 3}, breaks: true},
  {what: 'countdown, strict: left + used = cap', m: strict.machine, law: strict.laws[0]!, space: {depth: 3, bound: 3}, breaks: true},
  {what: 'countdown: the meter allows what it is sent', m: refines.machine, law: refines.stepLaws[0]!, space: {depth: 4, bound: 3}, breaks: false},
  // Interleaving: two a turns leave b's count; two turns of anyone don't.
  {what: "interleaved counters: two a turns leave b's count", m: counters, law: twoTurns, space: {depth: 3, bound: 2}, breaks: false},
  {what: "interleaved counters: two turns of anyone leave b's count", m: counters, law: {...twoTurns, name: "two turns of anyone leave b's count", when: undefined}, space: {depth: 3, bound: 2}, breaks: true},
  {what: 'interleaved counters: a.n <= cap', m: counters, law: counterLaws[0]!, space: {depth: 3, bound: 2}, breaks: false},
]
