// circuit breaker/arrow/OpeningStrategy.Count: extracted from arrow 2.3.0.1 (arrow-kt/arrow at 2.3.0.1), arrow-libs/resilience/arrow-resilience/src/commonMain/kotlin/arrow/resilience/CircuitBreaker.kt: CircuitBreaker.OpeningStrategy.Count (its init, shouldOpen, trackFailure, and OpeningStrategy.resetFailuresCount), checked against arrow-resilience-jvm-2.3.0.1.jar. Apache-2.0, (c) The Arrow Authors.
// Extracted by gdp-wired/extract from CircuitBreaker.kt (Count, a class and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, bool, int, Int, nat, oneOf, rule, when} from '../../../../core/dsl.ts'

export const countRule = rule("Count")
  .params({maxFailures0: nat, failuresCount0: int})
  .inputs({method: oneOf('shouldOpen', 'trackFailure', 'resetFailuresCount')})
  .state({maxFailures: ({maxFailures0}) => maxFailures0, failuresCount: int.from(({failuresCount0}) => failuresCount0), shouldOpen_result: bool.from(false)})
  .pre(({maxFailures0, failuresCount0}) => all(maxFailures0.atLeast(0), all(Int.of(maxFailures0).atLeast(-2147483648), maxFailures0.atMost(2147483647), failuresCount0.atLeast(-2147483648), failuresCount0.atMost(2147483647))))
  .step(({method, failuresCount, maxFailures}) => {
    const t1 = method.is('shouldOpen')
    const t2 = failuresCount.plus(1)
    return {failuresCount: when(t1, failuresCount, when(method.is('trackFailure'), when(t2.atLeast(2147483648), t2.minus(4294967296), t2), 0)), shouldOpen_result: all(t1, Int.of(maxFailures).lt(failuresCount))}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const countInvariants = [countRule.law("maxFailures within its type's range", ({maxFailures}) => maxFailures.atMost(2147483647)), countRule.law("failuresCount within its type's range", ({failuresCount}) => failuresCount.atMost(2147483647).and(failuresCount.atLeast(-2147483648)))]
