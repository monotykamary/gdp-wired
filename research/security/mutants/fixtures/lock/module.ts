import {Effect, Semaphore, TxRef} from 'effect'

// gdp: law only one grant: granted <= 1
export const make = Effect.gen(function* () {
  const consumed = yield* TxRef.make(0)
  const granted = yield* TxRef.make(0)
  const lock = yield* Semaphore.make(1)
  const claim = Effect.fn('claim')(function* () {
    yield* lock.withPermits(1)(Effect.gen(function* () {
      const current = yield* TxRef.get(consumed)
      if (current !== 0) return
      yield* TxRef.set(consumed, 1)
      yield* TxRef.update(granted, n => n + 1)
    }))
  })
  return {claim}
})
