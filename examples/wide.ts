// Yes/no state written under a wide condition: an alarm raised, and the system disarmed, when any of `pairs` sensor
// pairs both read past the limit while it is armed. Whether a step raises it is a condition of 2·pairs + 1 comparisons;
// that the alarm and `armed` stay yes/no (their kind laws) doesn't depend on which way it goes, since an if is at most
// the sum of its branches, so those proofs never decide it. (A law that reads which way it went, "never tripped while
// armed", does decide it, atom by atom.) For dsl.test.ts and lean-kernel/package-check.ts.
import {all, any, bool, nat, no, rule, when, yes, type Term} from '../core/dsl.ts'

export const wide = (pairs = 12) => rule('wide').params({limit: nat})
  .inputs(Object.fromEntries(Array.from({length: 2 * pairs}, (_, i) => [`s${i}`, nat])))
  .state({armed: bool.from(true), alarm: bool.from(false)})
  .step(env => {
    const s = (i: number) => (env as unknown as Record<string, Term>)[`s${i}`]!
    const raise = all(env.armed, any(...Array.from({length: pairs}, (_, i) => all(s(2 * i).gt(env.limit), s(2 * i + 1).gt(env.limit)))))
    return {alarm: when(raise, yes, env.alarm), armed: when(raise, no, env.armed)}
  })
