// Sizes of sets over a universe of names: for the suite (`bun examples/sizes.ts`), core/sizes.test.ts and
// lean-kernel/package-check.ts.
//
// A team over four names (interned 0 .. 3): a request carries a whole new roster, written at every key, accepted only if
// it is a set within the universe and at most `cap` names long. The team stays within the cap, and an accepted roster's
// size is the team's after the step. The broken variant checks the team's current size instead of the roster's.
import {type Law} from '../core/machine.ts'
import {everyKey, nat, rule, when} from '../core/dsl.ts'
import type {StepLaw} from '../kernel/kernel.ts'
import {proveStepLaws} from '../kernel/prove.ts'

export const NAMES = 4
export const team = (bug?: 'checks the current team') => rule('team roster').params({cap: nat}).maps({Team: 0}).carries('Roster')
  .flags(({cap, Roster, Team}) => ({accepted: Roster.within(NAMES).and((bug ? Team : Roster).sizeBelow(NAMES).atMost(cap))}))
  // A roster is a set: every cell 0 or 1.
  .assume(({Roster}) => everyKey(k => Roster.at(k).atMost(1)))
  .step(({accepted, Roster, Team}) => ({Team: Team.each(k => when(accepted, Roster.at(k), Team.at(k)))}))
const ok = team()
export const teamLaws = (r = ok): Law[] => [
  r.law('the team is within the universe', ({Team}) => Team.within(NAMES)),
  r.law('the team is within the cap', ({Team, cap}) => Team.sizeBelow(NAMES).atMost(cap)),
]
export const teamSteps = (r = ok): StepLaw[] => [
  r.stepLaw('an accepted roster is the team after, size and all', ({Roster}, after) => after.Team.sizeBelow(NAMES).eq(Roster.sizeBelow(NAMES)), ({accepted}) => accepted),
]

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const bug of [undefined, 'checks the current team'] as const) {
    const r = team(bug), v = proveStepLaws(r.machine, teamLaws(r), bug ? [] : teamSteps(r))
    if (!bug && !(v.proven && v.checked)) console.log(JSON.stringify(v.failed))
    results.push([`team roster${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
