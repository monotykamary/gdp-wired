// Functions from outside the rule, known to the kernel only by their facts: for the suite (`bun examples/functions.ts`),
// core/functions.test.ts and lean-kernel/package-check.ts.
//   - a per-minute limiter: a request's minute is its time divided by 60 (divBy), its count resets when the minute
//     moves on; the count stays within the cap and the minute within the time seen (from 60·q(t) <= t)
//   - a larger-of-two function written by hand (two arguments, paired into one key) with the fact it is given
//   - recursion defined in Lean: pairs n = n(n − 1)/2, by pairs 0 = 0 and pairs (n + 1) = pairs n + n; a room counts
//     the handshakes as people join, and the count is pairs of the people in it (proven from the two facts, which the
//     Lean export proves of the Lean definition)
import {type Law} from '../core/machine.ts'
import {divBy, fn, forall, max, nat, rule, when} from '../core/dsl.ts'
import {proveLaws} from '../kernel/prove.ts'

export const minutes = (bug?: 'keeps the raw time') => rule('per-minute limit').params({cap: nat}).inputs({t: nat}).state({minute: 0, count: 0, last: 0})
  .fns({perMinute: divBy(60)})
  // Requests come in time order.
  .assume(({t, last}) => t.atLeast(last))
  .flags(({t, minute, perMinute}) => ({fresh: perMinute(t).gt(minute)}))
  .step(({t, cap, minute, count, fresh, perMinute}) => {
    const n = when(fresh, 0, count)
    return {minute: when(fresh, bug ? t : perMinute(t), minute), count: when(n.lt(cap), n.plus(1), n), last: t}
  })
const ok = minutes()
export const minuteLaws = (r = ok): Law[] => [
  r.law('the count stays within the cap', ({count, cap}) => count.atMost(cap)),
  r.law('the minute is within the time seen', ({minute, last}) => minute.times(60).atMost(last)),
]

// The larger of two, by hand: its fact says it is at least the first. The mark is at least the last value seen.
export const larger = rule('high-water mark').inputs({a: nat}).state({high: 0, seen: 0})
  .fns({bigger: fn(2, (a: number, b: number) => (a < b ? b : a), {facts: f => ({'at least the first': forall(x => f(x, 0).atLeast(x))})})})
  .step(({a, high, bigger}) => ({high: max(bigger(a, 0), high), seen: a}))
export const largerLaws: Law[] = [larger.law('the mark is at least the last value seen', ({high, seen}) => seen.atMost(high))]

// pairs n: the number of pairs among n, as Lean defines it (`pairsLean`) and as the runtimes compute it.
export const pairsLean = {defs: 'def pairs : Nat → Nat\n  | 0 => 0\n  | n + 1 => pairs n + n', simp: ['pairs']}
export const room = (bug?: 'counts the newcomer too') => rule('handshakes').inputs({}).state({people: 0, shakes: 0})
  .fns({pairs: fn(1, 'x => x * (x - 1) / 2 + 0', {lean: 'pairs', facts: f => ({'pairs 0 = 0': f(0).eq(0), 'pairs (x + 1) = pairs x + x': forall(x => f(x.plus(1)).eq(f(x).plus(x)))})})})
  .step(({people, shakes}) => ({people: people.plus(1), shakes: shakes.plus(bug ? people.plus(1) : people)}))
export const roomLaws = (r = room()): Law[] => [r.law('the handshakes are the pairs of the people in the room', ({shakes, people, pairs}) => shakes.eq(pairs(people)))]

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const bug of [undefined, 'keeps the raw time'] as const) {
    const r = minutes(bug), v = proveLaws(r.machine, minuteLaws(r))
    results.push([`per-minute limit${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  const v = proveLaws(larger.machine, largerLaws)
  results.push(['high-water mark', v.proven && v.checked, true])
  for (const bug of [undefined, 'counts the newcomer too'] as const) {
    const r = room(bug), w = proveLaws(r.machine, roomLaws(r))
    results.push([`handshakes${bug ? ` (${bug})` : ''}`, w.proven && w.checked, !bug])
  }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
