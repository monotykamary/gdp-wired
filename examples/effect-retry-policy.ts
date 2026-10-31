// A retry policy and the lease it guards, written in Effect (v4) as a service is: the policy a capped, bounded
// exponential backoff; the lease's acquire retried with it while another holds the lease. examples/effect-retry.ts
// reads both with gdp-wired/effect and proves their laws (`npx gdp-wired-cli check examples/effect-retry-policy.ts`
// proves the laws written here).
import {Effect, Ref, Schedule, Schema} from 'effect'

// Doubling from 100 ms, never more than 2 s apart, at most 6 retries, none decided after 10 s.
// gdp: law the delay never exceeds the cap: delay <= 2000
// gdp: law never more than 6 retries: retries <= 6
// gdp: law it stops after the deadline: elapsed > 10000 implies done
export const backoff = Schedule.min([Schedule.exponential('100 millis'), Schedule.spaced('2 seconds')]).pipe(
  Schedule.upTo({times: 6, duration: '10 seconds'}),
)

export class Taken extends Schema.TaggedError<Taken>()('Taken', {holder: Schema.Number}) {}

export const make = Effect.gen(function* () {
  // 0 where the lease is free, else its holder.
  const holder = yield* Ref.make(0)
  const acquire = Effect.fn('Lease.acquire')(function* (who: number) {
    yield* Effect.gen(function* () {
      const h = yield* Ref.get(holder)
      if (who <= 0 || (h !== 0 && h !== who)) return yield* new Taken({holder: h})
      yield* Ref.set(holder, who)
    }).pipe(Effect.retry(backoff))
  })
  const release = Effect.fn('Lease.release')(function* (who: number) {
    const h = yield* Ref.get(holder)
    if (h === who) yield* Ref.set(holder, 0)
  })
  return {acquire, release}
})
