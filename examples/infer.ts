// Laws proven with invariants nobody wrote (core/infer.ts): for the suite (`bun examples/infer.ts`) and
// core/infer.test.ts. Each law holds but isn't inductive alone; inferLaws finds the laws that make it so, proves them
// with it, and says them as builder calls to paste.
//   - a connection pool: nothing is released that wasn't acquired, which needs in use + released <= acquired
//   - a token bucket: what is spent stays within 10 and 3 a tick, which needs tokens + spent <= 3·ticks + 10
//   - a lease: a lease another client holds has ended, which needs every lease to end by `until` (a law about every key)
//   - the pool with a release nobody checks: the law is false, and the search answers with the run that breaks it
import {type Law} from '../core/machine.ts'
import {forall, nat, oneOf, rule, when} from '../core/dsl.ts'
import {inferLaws} from '../core/infer.ts'

export const pool = (bug?: 'release unchecked') => rule('connection pool').params({size: nat})
  .inputs({op: oneOf('acquire', 'release')})
  .state({inUse: 0, acquired: 0, released: 0})
  .flags(({op, size, inUse}) => ({got: op.is('acquire').and(inUse.lt(size)), back: op.is('release').and(bug ? inUse.atLeast(0) : inUse.gt(0))}))
  .step(({inUse, acquired, released, got, back}) => ({
    inUse: when(got, inUse.plus(1), when(back, inUse.minus(1), inUse)),
    acquired: when(got, acquired.plus(1), acquired),
    released: when(back, released.plus(1), released),
  }))
export const poolLaw = (r = pool()): Law => r.law('released <= acquired', ({released, acquired}) => released.atMost(acquired))

export const bucket = () => rule('token bucket').inputs({op: oneOf('tick', 'spend'), amount: nat})
  .state({tokens: 10, spent: 0, ticks: 0})
  .step(({op, amount, tokens, spent, ticks}) => {
    const take = when(amount.atMost(tokens), amount, tokens)
    return {
      tokens: op.match({tick: () => when(tokens.plus(3).atMost(10), tokens.plus(3), 10), spend: () => tokens.minus(take)}),
      spent: op.match({tick: () => spent, spend: () => spent.plus(take)}),
      ticks: op.match({tick: () => ticks.plus(1), spend: () => ticks}),
    }
  })
export const bucketLaw = (r = bucket()): Law => r.law('spent <= 10 + 3 a tick', ({spent, ticks}) => spent.atMost(ticks.times(3).plus(10)))

export const lease = () => rule('lease').params({duration: nat})
  .inputs({op: oneOf('acquire', 'release', 'tick'), who: nat})
  .state({owner: 0, until: 0, now: 0})
  .maps({Expiry: 0})
  .flags(({op, who, owner, until, now}) => ({granted: op.is('acquire').and(who.eq(owner).or(until.atMost(now))), dropped: op.is('release').and(who.eq(owner))}))
  .step(({op, who, duration, until, now, owner, Expiry, granted, dropped}) => ({
    owner: when(granted, who, owner),
    until: when(granted, now.plus(duration), when(dropped, now, until)),
    now: when(op.is('tick'), now.plus(1), now),
    Expiry: Expiry.set(who, when(granted, now.plus(duration), when(dropped, now, Expiry.at(who)))),
  }))
export const leaseLaw = (r = lease()): Law => r.law('only the owner holds a live lease', ({Expiry, owner, now}) => forall(c => c.eq(owner).or(Expiry.at(c).atMost(now))))

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const [what, r, law] of [['connection pool', pool(), poolLaw], ['token bucket', bucket(), bucketLaw], ['lease', lease(), leaseLaw]] as const) {
    const v = inferLaws(r as never, [law(r as never)], [], {ms: 15000})
    results.push([what, v.proven && v.checked, true])
    for (const f of v.found) console.log(`     found: ${f.source ?? f.text}`)
  }
  const bad = pool('release unchecked'), bv = inferLaws(bad, [poolLaw(bad)], [], {ms: 15000})
  results.push(['connection pool (release unchecked)', bv.proven && bv.checked, false])
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
