// Extracted by gdp-wired/extract from Counts.go (Counts, a struct and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {oneOf, rule, when} from 'gdp-wired'

export const countsRule = rule("Counts")
  .inputs({method: oneOf('onRequest', 'onSuccess', 'onFailure', 'onExclusion', 'validRequests', 'clear')})
  .state({Requests: 0, TotalSuccesses: 0, TotalFailures: 0, TotalExclusions: 0, ConsecutiveSuccesses: 0, ConsecutiveFailures: 0, validRequests_result: 0})
  .step(({method, Requests, TotalSuccesses, TotalFailures, TotalExclusions, ConsecutiveSuccesses, ConsecutiveFailures}) => {
    const t1 = method.is('onRequest')
    const t2 = Requests.plus(1)
    const t3 = method.is('onSuccess')
    const t4 = method.is('onFailure')
    const t5 = method.is('onExclusion')
    const t6 = method.is('validRequests')
    const t7 = TotalSuccesses.plus(1)
    const t8 = TotalFailures.plus(1)
    const t9 = TotalExclusions.plus(1)
    const t10 = ConsecutiveSuccesses.plus(1)
    const t11 = ConsecutiveFailures.plus(1)
    return {Requests: when(t1, when(t2.atLeast(4294967296), t2.minus(4294967296), t2), when(t3, Requests, when(t4, Requests, when(t5, Requests, when(t6, Requests, 0))))), TotalSuccesses: when(t1, TotalSuccesses, when(t3, when(t7.atLeast(4294967296), t7.minus(4294967296), t7), when(t4, TotalSuccesses, when(t5, TotalSuccesses, when(t6, TotalSuccesses, 0))))), TotalFailures: when(t1, TotalFailures, when(t3, TotalFailures, when(t4, when(t8.atLeast(4294967296), t8.minus(4294967296), t8), when(t5, TotalFailures, when(t6, TotalFailures, 0))))), TotalExclusions: when(t1, TotalExclusions, when(t3, TotalExclusions, when(t4, TotalExclusions, when(t5, when(t9.atLeast(4294967296), t9.minus(4294967296), t9), when(t6, TotalExclusions, 0))))), ConsecutiveSuccesses: when(t1, ConsecutiveSuccesses, when(t3, when(t10.atLeast(4294967296), t10.minus(4294967296), t10), when(t4, 0, when(t5, ConsecutiveSuccesses, when(t6, ConsecutiveSuccesses, 0))))), ConsecutiveFailures: when(t1, ConsecutiveFailures, when(t3, 0, when(t4, when(t11.atLeast(4294967296), t11.minus(4294967296), t11), when(t5, ConsecutiveFailures, when(t6, ConsecutiveFailures, 0))))), validRequests_result: when(t1, 0, when(t3, 0, when(t4, 0, when(t5, 0, when(t6, when(Requests.lt(TotalExclusions), 0, Requests.minus(TotalExclusions)), 0)))))}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const countsInvariants = [countsRule.law("Requests within its type's range", ({Requests}) => Requests.atMost(4294967295).and(Requests.atLeast(0))), countsRule.law("TotalSuccesses within its type's range", ({TotalSuccesses}) => TotalSuccesses.atMost(4294967295).and(TotalSuccesses.atLeast(0))), countsRule.law("TotalFailures within its type's range", ({TotalFailures}) => TotalFailures.atMost(4294967295).and(TotalFailures.atLeast(0))), countsRule.law("TotalExclusions within its type's range", ({TotalExclusions}) => TotalExclusions.atMost(4294967295).and(TotalExclusions.atLeast(0))), countsRule.law("ConsecutiveSuccesses within its type's range", ({ConsecutiveSuccesses}) => ConsecutiveSuccesses.atMost(4294967295).and(ConsecutiveSuccesses.atLeast(0))), countsRule.law("ConsecutiveFailures within its type's range", ({ConsecutiveFailures}) => ConsecutiveFailures.atMost(4294967295).and(ConsecutiveFailures.atLeast(0))), countsRule.law("validRequests_result within its type's range", ({validRequests_result}) => validRequests_result.atMost(4294967295).and(validRequests_result.atLeast(0)))]
