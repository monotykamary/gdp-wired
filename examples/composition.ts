// Composition (core/compose.ts), proven by the kernel as it is. For the suite (`bun examples/composition.ts`),
// core/compose.test.ts and lean-kernel/export-kernel.ts (the Lean twin checks these machines like any other).
//   - refinement: a meter that counts down what is left refines the meter that counts up what is used
//   - interleaving: two capped counters, one moving per request; each keeps its cap, and two turns of one leave the other
//   - stuttering refinement: a meter that reserves, then charges, refines the meter that spends at once
//   - ghosts: an escrow where a refund never follows a release (at any distance), and a connection pool whose in-use
//     count is the total of every client's holdings
import {type C, type Law, type Machine, plus, x} from '../core/machine.ts'
import {min, nat, oneOf, rule, upTo, when, yes} from '../core/dsl.ts'
import {ever, ghost, interleave, refinement, side, total} from '../core/compose.ts'
import type {StepLaw} from '../kernel/kernel.ts'
import {proveLaws, proveStepLaws} from '../kernel/prove.ts'
import {domains} from './index.ts'

// The spec only takes spends up to `most`; the implementation counts down what is left and clamps each spend to `most`
// first, so every request it takes is one the spec allows.
export const meter = rule('meter').params({cap: nat, most: nat}).inputs({amount: nat}).state({used: 0})
  .assume(({amount, most}) => amount.atMost(most))
  .flags(({amount, used, cap}) => ({fits: used.plus(amount).atMost(cap)}))
  .step(({used, amount, fits}) => ({used: when(fits, used.plus(amount), used)}))
export const countdown = (bug?: 'no clamp' | 'strict') => rule('meter, counting down').params({cap: nat, most: nat}).inputs({amount: nat}).state({left: ({cap}) => cap})
  .step(({left, amount, most}) => {
    const spend = bug === 'no clamp' ? amount : min(amount, most)
    return {left: when(bug === 'strict' ? spend.lt(left) : spend.atMost(left), left.minus(spend), left)}
  })
export const meterRelation: Law[] = [{name: 'left + used = cap', holds: {op: '=', a: plus(x('a_left'), x('b_used')), b: x('cap')}}]
export const meterRefinement = (bug?: 'no clamp' | 'strict') => refinement(countdown(bug).machine, meter.machine, {
  relation: meterRelation,
  witness: {amount: bug === 'no clamp' ? x('amount') : {op: 'min', a: x('amount'), b: x('most')}},
})

// Two capped counters, interleaved.
export const counter = rule('counter').params({cap: upTo(10)}).inputs({amount: nat}).state({n: 0})
  .step(({n, amount, cap}) => ({n: when(n.plus(amount).atMost(cap), n.plus(amount), n)}))
export const counters: Machine = interleave(counter.machine, counter.machine)
export const counterLaws: Law[] = (['a_', 'b_'] as const).map(p => ({name: `${p[0]}.n <= cap`, holds: side(counter.machine, p, {op: '<=', a: x('n'), b: x('cap')})}))
const aTurn: C = {op: '=', a: x('turn'), b: {op: 'const', value: 0}}
export const counterSteps: StepLaw[] = [
  {name: "an a turn leaves b's count", when: aTurn, then: {op: '=', a: x("b_n'"), b: x('b_n')}},
  {name: "two a turns leave b's count", steps: 2, when: [aTurn, aTurn], then: {op: '=', a: x("b_n'"), b: x('b_n')}},
]

// A meter that reserves a spend (clamped to `most`) and charges it later refines the meter that spends at once: a
// reserve is a step the spec doesn't see, and a charge sends the spec the reserved amount. Charging the request's amount
// instead drifts from the spec.
export const twoPhase = (bug?: 'charges the request') => rule('meter, two-phase').params({cap: nat, most: nat}).inputs({op: oneOf('reserve', 'charge'), amount: nat}).state({used: 0, pending: 0})
  .step(({op, amount, most, cap, used, pending}) => {
    const charged = bug === 'charges the request' ? amount : pending
    return {pending: when(op.is('reserve'), min(amount, most), when(op.is('charge'), 0, pending)), used: when(op.is('charge').and(used.plus(charged).atMost(cap)), used.plus(charged), used)}
  })
const isReserve: C = {op: '=', a: x('op'), b: {op: 'const', value: 0}}
export const twoPhaseRefinement = (bug?: 'charges the request') => refinement(twoPhase(bug).machine, meter.machine, {
  relation: [{name: 'used = used', holds: {op: '=', a: x('a_used'), b: x('b_used')}}, {name: 'pending <= most', holds: {op: '<=', a: x('a_pending'), b: x('most')}}],
  witness: {amount: x('a_pending')}, stutter: isReserve,
})

// An escrow: deposits add to what it holds, a release pays it out and closes it, a refund returns it. Once released,
// nothing may be refunded, however many steps later: a ghost remembers that a release happened, and a step law says no
// refund is paid after it. Reopening on a deposit after the release lets one through (deposit, release, deposit, refund).
export const escrow = (bug?: 'reopens on a deposit') => rule('escrow').inputs({op: oneOf('deposit', 'release', 'refund'), amount: nat}).state({held: 0, closed: 0, refunded: 0})
  .flags(({op, held, closed}) => ({releasing: op.is('release').and(closed.eq(0), held.gt(0)), refunding: op.is('refund').and(held.gt(0), bug === 'reopens on a deposit' ? yes : closed.eq(0))}))
  .step(({op, amount, held, closed, refunded, releasing, refunding}) => ({
    held: when(op.is('deposit').and(bug === 'reopens on a deposit' ? yes : closed.eq(0)), held.plus(amount), when(releasing.or(refunding), 0, held)),
    closed: when(releasing, 1, closed),
    refunded: when(refunding, refunded.plus(held), refunded),
  }))
export const escrowWatched = (bug?: 'reopens on a deposit') => ghost(escrow(bug).machine, {released: ever('released', {op: 'flag', name: 'releasing'})})
export const escrowLaws: Law[] = [{name: 'a release closes it', holds: {op: '<=', a: x('released'), b: x('closed')}}]
export const escrowSteps: StepLaw[] = [{name: 'no refund after a release', then: {op: 'or', xs: [{op: '=', a: x('released'), b: {op: 'const', value: 0}}, {op: '=', a: x("refunded'"), b: x('refunded')}]}}]

// The connection pool (examples/domains/operations.ts), its holdings totalled by a ghost: in use is exactly what the
// clients hold between them, a law about every key at once. Releasing without checking the client holds one breaks it.
const poolCase = domains.find(d => d.domain === 'operations')!.cases.find(c => c.name === 'connection pool')!
if (poolCase.kind !== 'rule') throw new Error('the connection pool is a rule')
const poolOf = (bug?: string) => (bug ? poolCase.broken.find(b => b.name === bug)!.rule : poolCase.rule).machine as Machine
export const pooled = (bug?: 'release unchecked') => { const m = poolOf(bug); return ghost(m, {heldTotal: total(m, 'Held', 'heldTotal')}) }
export const poolLaws: Law[] = poolCase.laws
export const poolTotal: Law[] = [{name: 'in use = what the clients hold', holds: {op: '=', a: x('inUse'), b: x('heldTotal')}}]

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  const ok = meterRefinement()
  const r = proveStepLaws(ok.machine, ok.laws, ok.stepLaws)
  results.push(['countdown refines meter', r.proven && r.checked, true])
  for (const bug of ['no clamp', 'strict'] as const) {
    const b = meterRefinement(bug)
    results.push([`countdown (${bug}) refines meter`, proveStepLaws(b.machine, b.laws, b.stepLaws).proven, false])
  }
  const c = proveStepLaws(counters, counterLaws, counterSteps)
  results.push(['interleaved counters', c.proven && c.checked, true])
  for (const bug of [undefined, 'charges the request'] as const) {
    const t = twoPhaseRefinement(bug), v = proveStepLaws(t.machine, t.laws, t.stepLaws)
    results.push([`two-phase${bug ? ` (${bug})` : ''} refines meter`, v.proven && v.checked, !bug])
  }
  for (const bug of [undefined, 'reopens on a deposit'] as const) {
    const v = proveStepLaws(escrowWatched(bug), escrowLaws, escrowSteps)
    results.push([`escrow${bug ? ` (${bug})` : ''}: no refund after a release`, v.proven && v.checked, !bug])
  }
  for (const bug of [undefined, 'release unchecked'] as const) {
    const v = proveLaws(pooled(bug), [...poolLaws, ...poolTotal])
    results.push([`pool${bug ? ` (${bug})` : ''}: in use = total held`, v.proven && v.checked, !bug])
  }
  for (const [what, got, want] of results) console.log(`${what.padEnd(34)} ${got ? 'proven, kernel accepts' : 'not proven'}${got === want ? '' : '   UNEXPECTED'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
