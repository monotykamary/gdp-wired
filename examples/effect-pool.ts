// A worker pool in Effect (v4): jobs wait in a bounded queue of 4, at most two run at once (a Semaphore of 2, a permit
// held around each job), and the work done is added up. gdp-wired/effect reads it with the Queue and the Semaphore
// modelled (core/effect-prims.ts), their own laws proven once; examples/effect-queue.ts proves the laws written here,
// breaks the pool and runs it, and `npx gdp-wired-cli check examples/effect-pool.ts` proves them from these comments.
import {Effect, Queue, Ref, Schema, Semaphore} from 'effect'

export class BadJob extends Schema.TaggedError<BadJob>()('BadJob', {cost: Schema.Number}) {}

// gdp: law every job waiting costs 1 to 10: forall k in jobs_items: (jobs_head <= k and k < jobs_tail) implies (1 <= jobs_items[k] and jobs_items[k] <= 10)
// gdp: law the work done never goes negative: spent >= 0
// gdp: law no permit is given back that wasn't taken: workers_taken >= 0
export const make = Effect.gen(function* () {
  const jobs = yield* Queue.bounded<number>(4)
  const workers = yield* Semaphore.make(2)
  const spent = yield* Ref.make(0)
  // A job of 1 to 10 units, queued (an offer to the full queue waits for room).
  const submit = Effect.fn('Pool.submit')(function* (cost: number) {
    if (cost < 1 || cost > 10) return yield* new BadJob({cost})
    return yield* Queue.offer(jobs, cost)
  })
  // A worker: one of the two permits, the oldest job (waiting for one), its work, the permit back.
  const work = Effect.fn('Pool.work')(function* () {
    yield* workers.withPermits(1)(Effect.gen(function* () {
      const cost = yield* Queue.take(jobs)
      yield* Effect.sleep('10 millis')
      yield* Ref.update(spent, s => s + cost)
    }))
  })
  const backlog = Effect.fn('Pool.backlog')(function* () {
    return yield* Queue.size(jobs)
  })
  return {submit, work, backlog}
})
