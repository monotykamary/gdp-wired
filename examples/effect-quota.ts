// A daily quota written in Effect (v4), as a service is: its state a Ref of a map, its methods Effect.fn bodies, a
// typed failure, the time from Clock. examples/effect.ts reads it with gdp-wired/effect and proves its laws.
import {Clock, Context, Effect, Layer, Ref, Schema} from 'effect'

export const DAY = 86_400_000

export class QuotaExceeded extends Schema.TaggedError<QuotaExceeded>()('QuotaExceeded', {user: Schema.String, used: Schema.Number}) {}

interface Usage {
  readonly used: number
  readonly windowStart: number
}

export class Quota extends Context.Service<Quota, {
  readonly spend: (user: string, units: number) => Effect.Effect<number, QuotaExceeded>
  readonly refund: (user: string, units: number) => Effect.Effect<void>
}>()('example/Quota') {}

export const make = (limit: number) => Effect.gen(function* () {
  if (limit < 0) return yield* Effect.die('a quota of less than nothing')
  const usage = yield* Ref.make<ReadonlyMap<string, Usage>>(new Map())

  // Spends units of the user's quota for the day its window started; a new window starts a day after the last.
  const spend = Effect.fn('Quota.spend')(function* (user: string, units: number) {
    if (units <= 0) return yield* new QuotaExceeded({user, used: 0})
    const now = yield* Clock.currentTimeMillis
    const current = (yield* Ref.get(usage)).get(user)
    const open = current !== undefined && now >= current.windowStart && now - current.windowStart < DAY
    const used = open ? current.used : 0
    if (used + units > limit) return yield* new QuotaExceeded({user, used})
    yield* Ref.update(usage, m => new Map(m).set(user, {used: used + units, windowStart: open ? current.windowStart : now}))
    return limit - used - units
  })

  // Gives units back (a request that failed downstream), never below none.
  const refund = (user: string, units: number) => Ref.update(usage, m => {
    const current = m.get(user)
    if (current === undefined || units <= 0) return m
    return new Map(m).set(user, {...current, used: Math.max(0, current.used - units)})
  })

  return Quota.of({spend, refund})
})

export const layer = (limit: number) => Layer.effect(Quota, make(limit))
