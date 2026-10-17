// Searches for step laws and k-step laws: the examples' own laws and broken variants, and the composition examples, each
// a machine and the law the kernel is asked to prove. A broken one must turn up a run that breaks its law (replayed by
// core/watch.ts); a proven one must turn up nothing within its space.
import type {Law, Machine} from '../core/machine.ts'
import {size} from '../search/compile.ts'
import type {Watched} from '../core/watch.ts'
import type {StepLaw} from '../kernel/kernel.ts'
import type {Space} from './compile.ts'
import {domains} from '../examples/index.ts'
import {authority, authorityLaws, authoritySteps} from '../examples/sets.ts'
import {counterLaws, counterSteps, counters, escrowSteps, escrowWatched, meterRefinement, poolTotal, pooled, twoPhaseRefinement} from '../examples/composition.ts'
import {minuteLaws, minutes, room, roomLaws} from '../examples/functions.ts'

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
const phased = twoPhaseRefinement(), phasedBad = twoPhaseRefinement('charges the request')

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
  // Stuttering refinement: charging the request's amount instead of the reserved one drifts from the spec.
  {what: 'two-phase, charges the request: used = used', m: phasedBad.machine, law: phasedBad.laws[0]!, space: {depth: 3, bound: 2}, breaks: true},
  {what: 'two-phase: used = used', m: phased.machine, law: phased.laws[0]!, space: {depth: 4, bound: 2}, breaks: false},
  // Ghosts: a refund after a release, four steps in (deposit, release, deposit, refund); in use against the total held.
  {what: 'escrow, reopens on a deposit: no refund after a release', m: escrowWatched('reopens on a deposit'), law: escrowSteps[0]!, space: {depth: 4, bound: 2}, breaks: true},
  {what: 'escrow: no refund after a release', m: escrowWatched(), law: escrowSteps[0]!, space: {depth: 5, bound: 2}, breaks: false},
  {what: 'pool, release unchecked: in use = what the clients hold', m: pooled('release unchecked'), law: poolTotal[0]!, space: {depth: 3, bound: 1}, breaks: true},
  {what: 'pool: in use = what the clients hold', m: pooled(), law: poolTotal[0]!, space: {depth: 4, bound: 1}, breaks: false},
  // Functions, tabulated over the keys they can be read at: the minute as the raw time breaks its law at the first
  // request past a minute (times up to 60); the handshakes counting the newcomer too break theirs at the first join.
  {what: 'per-minute limit, keeps the raw time: the minute is within the time seen', m: minutes('keeps the raw time').machine, law: minuteLaws(minutes('keeps the raw time'))[1]!, space: {depth: 1, bound: 60}, breaks: true},
  {what: 'per-minute limit: the minute is within the time seen', m: minutes().machine, law: minuteLaws()[1]!, space: {depth: 2, bound: 60}, breaks: false},
  {what: 'handshakes, counting the newcomer too: shakes = pairs(people)', m: room('counts the newcomer too').machine, law: roomLaws(room('counts the newcomer too'))[0]!, space: {depth: 4, bound: 1}, breaks: true},
  {what: 'handshakes: shakes = pairs(people)', m: room().machine, law: roomLaws()[0]!, space: {depth: 5, bound: 1}, breaks: false},
]

// Every example rule with a history, its proven laws and its broken variants: the queries come from the log in registers.
// A proven rule must have no run that breaks a law; a broken variant must have one that breaks some law (the examples'
// harness finds it on random runs; here, within the space).
export type HistorySearch = {what: string, m: Machine, laws: Law[], space: Space, breaks: boolean}
export const historySearches = (budget = 2_000_000): HistorySearch[] => domains.flatMap(d => d.cases.flatMap(c => {
  if (c.kind !== 'rule' || !c.rule.machine.history) return []
  const variants = [{name: '', m: c.rule.machine as Machine, laws: c.laws, breaks: false}, ...c.broken.map(b => ({name: b.name, m: b.rule.machine as Machine, laws: b.laws, breaks: true}))]
  return variants.map(v => {
    // The deepest space within the budget, values 0..2 (0..1 if 0..2 doesn't reach depth 3).
    const space = (bound: number) => { let depth = 1; while (depth < 8 && size(v.m, {depth: depth + 1, bound}) <= budget) depth++; return {depth, bound} }
    const s2 = space(2)
    return {what: `${d.domain} / ${c.name}${v.name ? `, ${v.name}` : ''}`, m: v.m, laws: v.laws, space: s2.depth >= 3 ? s2 : space(1), breaks: v.breaks}
  })
}))

// Sets: the derived authority (examples/sets.ts), its laws and step laws, and its broken variants; a request carries a
// set (one digit per cell). The space grows fast (each step's request is its inputs and a cell per name), so the CPU
// check samples documents and the GPU runs every one.
export type SetSearch = {what: string, m: Machine, law: Watched, space: Space, breaks: boolean}
export const setSearches = (space: Space = {depth: 3, bound: 3}): SetSearch[] => {
  const variants = [{name: '', a: authority()}, {name: 'checks only the named grant', a: authority('checks only the named grant')}, {name: 'keeps the child on refusal', a: authority('keeps the child on refusal')}]
  return variants.flatMap(v => {
    const all: Watched[] = [...authorityLaws(v.a), ...authoritySteps(v.a)]
    // A broken variant breaks the law its proof fails at (kernel/sets.test.ts).
    const breaking = v.name === 'checks only the named grant' ? 'the child is within the grants' : v.name === 'keeps the child on refusal' ? 'a refused derivation leaves no live child' : undefined
    return all.filter(l => !v.name || l.name === breaking).map(law => ({what: `derived authority${v.name ? `, ${v.name}` : ''}: ${law.name}`, m: v.a.machine, law, space, breaks: !!v.name}))
  })
}
