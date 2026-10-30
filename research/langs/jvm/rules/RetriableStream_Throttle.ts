// rate limit/grpc-java/RetriableStream.Throttle: extracted from grpc-java 1.85.1 (grpc/grpc-java at v1.85.1), core/src/main/java/io/grpc/internal/RetriableStream.java: RetriableStream.Throttle (constructor, isAboveThreshold, onQualifiedFailureThenCheckIsAboveThreshold, onSuccess), checked against grpc-core-1.85.1.jar. Apache-2.0, (c) The gRPC Authors.
// Extracted by gdp-wired/extract from RetriableStream.java (Throttle, a class and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, bool, int, oneOf, rule, when} from '../../../../core/dsl.ts'

export const throttleRule = rule("Throttle")
  .params({maxTokens0: int, tokenRatio0: int, maxTokens0_div2: int, maxTokens0_div2_: int})
  .inputs({method: oneOf('isAboveThreshold', 'onQualifiedFailureThenCheckIsAboveThreshold', 'onSuccess')})
  .state({maxTokens: int.from(({maxTokens0}) => when(maxTokens0.times(1000).lt(-2147483648), -2147483648, when(maxTokens0.times(1000).gt(2147483647), 2147483647, maxTokens0.times(1000)))), threshold: int.from(({maxTokens0, maxTokens0_div2, maxTokens0_div2_}) => when(when(maxTokens0.times(1000).lt(-2147483648), -2147483648, when(maxTokens0.times(1000).gt(2147483647), 2147483647, maxTokens0.times(1000))).atLeast(0), maxTokens0_div2, maxTokens0_div2_.negate())), tokenRatio: int.from(({tokenRatio0}) => when(tokenRatio0.times(1000).lt(-2147483648), -2147483648, when(tokenRatio0.times(1000).gt(2147483647), 2147483647, tokenRatio0.times(1000)))), tokenCount: int.from(({maxTokens0}) => when(maxTokens0.times(1000).lt(-2147483648), -2147483648, when(maxTokens0.times(1000).gt(2147483647), 2147483647, maxTokens0.times(1000)))), isAboveThreshold_result: bool.from(false), onQualifiedFailureThenCheckIsAboveThreshold_result: bool.from(false)})
  .pre(({maxTokens0, tokenRatio0, maxTokens0_div2, maxTokens0_div2_}) => all(all(maxTokens0.atLeast(-16777216), maxTokens0.atMost(16777215), tokenRatio0.atLeast(-16777216), tokenRatio0.atMost(16777215)), maxTokens0_div2.times(2).atMost(when(maxTokens0.times(1000).lt(-2147483648), -2147483648, when(maxTokens0.times(1000).gt(2147483647), 2147483647, maxTokens0.times(1000)))), when(maxTokens0.times(1000).lt(-2147483648), -2147483648, when(maxTokens0.times(1000).gt(2147483647), 2147483647, maxTokens0.times(1000))).lt(maxTokens0_div2.times(2).plus(2)), maxTokens0_div2_.times(2).atMost(when(maxTokens0.times(1000).lt(-2147483648), -2147483648, when(maxTokens0.times(1000).gt(2147483647), 2147483647, maxTokens0.times(1000))).negate()), when(maxTokens0.times(1000).lt(-2147483648), -2147483648, when(maxTokens0.times(1000).gt(2147483647), 2147483647, maxTokens0.times(1000))).negate().lt(maxTokens0_div2_.times(2).plus(2))))
  .step(({method, tokenCount, maxTokens, tokenRatio, threshold}) => {
    const t1 = method.is('isAboveThreshold')
    const t2 = method.is('onQualifiedFailureThenCheckIsAboveThreshold')
    const t3 = tokenCount.eq(0)
    const t4 = tokenCount.minus(1000)
    const t5 = when(t4.atLeast(-2147483648), t4, t4.plus(4294967296))
    const t6 = tokenCount.plus(tokenRatio)
    return {tokenCount: when(t1, tokenCount, when(t2, when(t3, tokenCount, t5.clamped), when(tokenCount.eq(maxTokens), tokenCount, when(t6.atLeast(2147483648), t6.minus(4294967296), when(t6.atLeast(-2147483648), t6, t6.plus(4294967296))).min(maxTokens)))), isAboveThreshold_result: all(t1, threshold.lt(tokenCount)), onQualifiedFailureThenCheckIsAboveThreshold_result: all(t2, tokenCount.eq(0).not(), threshold.lt(t5))}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const throttleInvariants = [throttleRule.law("maxTokens within its type's range", ({maxTokens}) => maxTokens.atMost(2147483647).and(maxTokens.atLeast(-2147483648))), throttleRule.law("threshold within its type's range", ({threshold}) => threshold.atMost(2147483647).and(threshold.atLeast(-2147483648))), throttleRule.law("tokenRatio within its type's range", ({tokenRatio}) => tokenRatio.atMost(2147483647).and(tokenRatio.atLeast(-2147483648))), throttleRule.law("tokenCount within its type's range", ({tokenCount}) => tokenCount.atMost(2147483647).and(tokenCount.atLeast(-2147483648)))]
