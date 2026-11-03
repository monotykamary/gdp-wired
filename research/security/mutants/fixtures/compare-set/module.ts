import {Effect, TxRef} from 'effect'

// gdp: law only one grant: granted <= 1
export const make = Effect.gen(function* () {
  const consumed = yield* TxRef.make(0)
  const granted = yield* TxRef.make(0)
  const claim = Effect.fn('claim')(function* () {
    const accepted = yield* TxRef.modify(consumed, current => [current === 0, current === 0 ? 1 : current] as const)
    if (accepted) yield* TxRef.update(granted, n => n + 1)
  })
  return {claim}
})
