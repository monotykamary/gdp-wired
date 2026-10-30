// rate limit/okhttp/WindowCounter: extracted from okhttp 5.5.1 (square/okhttp at parent-5.5.1), okhttp/src/commonJvmAndroid/kotlin/okhttp3/internal/http2/flowcontrol/WindowCounter.kt: WindowCounter(streamId), update(total, acknowledged), unacknowledged. Apache-2.0, (c) Square, Inc..
// Extracted by gdp-wired/extract from WindowCounter.kt (WindowCounter, a class and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, any, bool, int, oneOf, rule, when} from '../../../../core/dsl.ts'

export const windowCounterRule = rule("WindowCounter")
  .params({streamId0: int})
  .inputs({method: oneOf('update', 'unacknowledged'), update_total: int, update_acknowledged: int})
  .state({streamId: int.from(({streamId0}) => streamId0), total: int.from(0), acknowledged: int.from(0), unacknowledged_result: int.from(0), failed: bool.from(false)})
  .pre(({streamId0}) => all(streamId0.atLeast(-2147483648), streamId0.atMost(2147483647)))
  .step(({method, update_total, update_acknowledged, acknowledged, total}) => {
    const t1 = method.is('update')
    const t2 = update_total.atLeast(0)
    const t3 = update_acknowledged.atLeast(0)
    const t4 = acknowledged.plus(update_acknowledged)
    const t5 = total.plus(update_total)
    const t6 = t4.atMost(t5)
    const t7 = all(t2, t3, t6)
    return {total: when(t1, when(t7, t5, when(t2, when(t3, t5, total), total)), total), acknowledged: when(t1, when(t7, t4, when(t2, when(t3, t4, acknowledged), acknowledged)), acknowledged), unacknowledged_result: when(t1, 0, when(method.is('unacknowledged'), total.minus(acknowledged), 0)), failed: all(t1, any(all(t1, update_total.lt(0)), all(t1, t2, update_acknowledged.lt(0)), all(t1, t2, t3, t5.lt(t4))))}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const windowCounterInvariants = [windowCounterRule.law("streamId within its type's range", ({streamId}) => streamId.atMost(2147483647).and(streamId.atLeast(-2147483648)))]
