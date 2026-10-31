// Two accounts in Effect (v4) as a service is: their balances in TxRefs, each method one transaction (Effect.tx), a
// spend that waits for the savings to cover it (Effect.txRetry), a save retried with a capped backoff. examples/
// effect-stm.ts reads it with gdp-wired/effect and proves its laws; `npx gdp-wired-cli check examples/effect-bank.ts`
// proves the laws written here, the schedule's and the service's.
import {Effect, Schedule, Schema, TxRef} from 'effect'

// Doubling from 100 ms, never more than 2 s apart, at most 5 retries, none decided after 10 s.
// gdp: law the delay never exceeds the cap: delay <= 2000
// gdp: law never more than 5 retries: retries <= 5
// gdp: law it stops after the deadline: elapsed > 10000 implies done
export const backoff = Schedule.min([Schedule.exponential('100 millis'), Schedule.spaced('2 seconds')]).pipe(
  Schedule.upTo({times: 5, duration: '10 seconds'}),
)

export class Insufficient extends Schema.TaggedError<Insufficient>()('Insufficient', {amount: Schema.Number}) {}

// 100 between the two accounts: save moves some from checking to savings, spend moves it back.
// gdp: law the money is conserved: checking + savings == 100
// gdp: law checking is never overdrawn: checking >= 0
export const make = Effect.gen(function* () {
  const checking = yield* TxRef.make(100)
  const savings = yield* TxRef.make(0)
  const save = Effect.fn('Bank.save')(function* (amount: number) {
    if (amount < 0) return yield* new Insufficient({amount})
    yield* Effect.tx(Effect.gen(function* () {
      const balance = yield* TxRef.get(checking)
      if (balance < amount) return yield* new Insufficient({amount})
      yield* TxRef.set(checking, balance - amount)
      yield* TxRef.update(savings, s => s + amount)
    })).pipe(Effect.retry(backoff))
  })
  // Waits (the transaction retries when savings change) until savings cover the amount.
  const spend = Effect.fn('Bank.spend')(function* (amount: number) {
    if (amount < 0) return yield* new Insufficient({amount})
    yield* Effect.tx(Effect.gen(function* () {
      const s = yield* TxRef.get(savings)
      if (s < amount) return yield* Effect.txRetry
      yield* TxRef.set(savings, s - amount)
      yield* TxRef.update(checking, c => c + amount)
    }))
  })
  return {save, spend}
})
