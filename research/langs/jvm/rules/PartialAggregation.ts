// circuit breaker/resilience4j/PartialAggregation: extracted from resilience4j 2.4.0 (resilience4j/resilience4j at v2.4.0), resilience4j-core/src/main/java/io/github/resilience4j/core/metrics/PartialAggregation.java (and AbstractAggregation.java, its superclass): PartialAggregation(epochSecond), record(duration, durationUnit, outcome), reset(epochSecond). Apache-2.0, (c) Robert Winkler and Bohdan Storozhuk.
// Extracted by gdp-wired/extract from PartialAggregation.java (PartialAggregation, a class and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {int, oneOf, rule, when} from '../../../../core/dsl.ts'

export const partialAggregationRule = rule("PartialAggregation")
  .params({epochSecond0: int})
  .inputs({method: oneOf('record', 'reset'), record_duration: int, record_durationUnit: oneOf('NANOSECONDS', 'MICROSECONDS', 'MILLISECONDS', 'SECONDS', 'MINUTES', 'HOURS', 'DAYS'), record_outcome: oneOf('SUCCESS', 'ERROR', 'SLOW_SUCCESS', 'SLOW_ERROR'), reset_epochSecond: int})
  .state({totalDurationInMillis: int.from(0), numberOfSlowCalls: int.from(0), numberOfSlowFailedCalls: int.from(0), numberOfFailedCalls: int.from(0), numberOfCalls: int.from(0), epochSecond: int.from(({epochSecond0}) => epochSecond0)})
  .step(({method, totalDurationInMillis, record_durationUnit, record_duration, record_outcome, numberOfSlowCalls, numberOfSlowFailedCalls, numberOfFailedCalls, numberOfCalls, epochSecond, reset_epochSecond}) => {
    const t1 = method.is('record')
    const t2 = record_duration.atLeast(0)
    const t3 = record_outcome.is('SLOW_SUCCESS')
    const t4 = numberOfSlowCalls.plus(1)
    const t5 = when(t4.atLeast(2147483648), t4.minus(4294967296), t4)
    const t6 = record_outcome.is('SLOW_ERROR')
    const t7 = numberOfSlowFailedCalls.plus(1)
    const t8 = numberOfFailedCalls.plus(1)
    const t9 = when(t8.atLeast(2147483648), t8.minus(4294967296), t8)
    const t10 = numberOfCalls.plus(1)
    return {totalDurationInMillis: when(t1, totalDurationInMillis.plus(when(record_durationUnit.is('NANOSECONDS'), when(t2, record_duration.divBy(1000000), record_duration.negate().divBy(1000000).negate()), when(record_durationUnit.is('MICROSECONDS'), when(t2, record_duration.divBy(1000), record_duration.negate().divBy(1000).negate()), when(record_durationUnit.is('MILLISECONDS'), record_duration, when(record_durationUnit.is('SECONDS'), record_duration.times(1000), when(record_durationUnit.is('MINUTES'), record_duration.times(60000), when(record_durationUnit.is('HOURS'), record_duration.times(3600000), record_duration.times(86400000)))))))), 0), numberOfSlowCalls: when(t1, when(t3, t5, when(t6, t5, numberOfSlowCalls)), 0), numberOfSlowFailedCalls: when(t1, when(t3, numberOfSlowFailedCalls, when(t6, when(t7.atLeast(2147483648), t7.minus(4294967296), t7), numberOfSlowFailedCalls)), 0), numberOfFailedCalls: when(t1, when(t3, numberOfFailedCalls, when(t6, t9, when(record_outcome.is('ERROR'), t9, numberOfFailedCalls))), 0), numberOfCalls: when(t1, when(t10.atLeast(2147483648), t10.minus(4294967296), t10), 0), epochSecond: when(t1, epochSecond, reset_epochSecond)}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const partialAggregationInvariants = [partialAggregationRule.law("numberOfSlowCalls within its type's range", ({numberOfSlowCalls}) => numberOfSlowCalls.atMost(2147483647).and(numberOfSlowCalls.atLeast(-2147483648))), partialAggregationRule.law("numberOfSlowFailedCalls within its type's range", ({numberOfSlowFailedCalls}) => numberOfSlowFailedCalls.atMost(2147483647).and(numberOfSlowFailedCalls.atLeast(-2147483648))), partialAggregationRule.law("numberOfFailedCalls within its type's range", ({numberOfFailedCalls}) => numberOfFailedCalls.atMost(2147483647).and(numberOfFailedCalls.atLeast(-2147483648))), partialAggregationRule.law("numberOfCalls within its type's range", ({numberOfCalls}) => numberOfCalls.atMost(2147483647).and(numberOfCalls.atLeast(-2147483648)))]
