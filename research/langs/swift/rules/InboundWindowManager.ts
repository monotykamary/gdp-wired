// flow control/swift-nio-http2/InboundWindowManager: extracted from swift-nio-http2 1.46.0 (apple/swift-nio-http2 at 1.46.0), Sources/NIOHTTP2/InboundWindowManager.swift: InboundWindowManager (init(targetSize:), newWindowSize, initialWindowSizeChanged, bufferedFrameReceived, bufferedFrameEmitted, and calculateWindowIncrement inlined). Apache-2.0, (c) Apple Inc. and the SwiftNIO project authors.
// Extracted by gdp-wired/extract from InboundWindowManager.swift (InboundWindowManager, a class and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, any, bool, int, not, oneOf, rule, when} from '../../../../core/dsl.ts'

export const inboundWindowManagerRule = rule("InboundWindowManager")
  .params({targetSize: int})
  .inputs({method: oneOf('newWindowSize', 'initialWindowSizeChanged', 'bufferedFrameReceived', 'bufferedFrameEmitted'), newWindowSize_newSize: int, initialWindowSizeChanged_delta: int, bufferedFrameReceived_size: int, bufferedFrameEmitted_size: int})
  .state({lastWindowSize: int.from(0), lastWindowSize_none: bool.from(true), bufferedBytes: int.from(0), closed: bool.from(false), targetWindowSize: int.from(({targetSize}) => targetSize), newWindowSize_result: int.from(0), newWindowSize_result_none: bool.from(false), initialWindowSizeChanged_result: int.from(0), initialWindowSizeChanged_result_none: bool.from(false), bufferedFrameEmitted_result: int.from(0), bufferedFrameEmitted_result_none: bool.from(false)})
  .pre(({targetSize}) => all(all(targetSize.atMost(2147483647), targetSize.atMost(2147483647).implies(targetSize.atLeast(0))), all(targetSize.atLeast(-2147483648), targetSize.atMost(2147483647))))
  .assume(({method, closed, targetWindowSize, newWindowSize_newSize, bufferedBytes, initialWindowSizeChanged_delta, bufferedFrameEmitted_size, lastWindowSize_none, lastWindowSize}) => all(not(all(method.is('newWindowSize'), not(closed), newWindowSize_newSize.plus(bufferedBytes).lt(targetWindowSize), newWindowSize_newSize.plus(bufferedBytes).atLeast(0), newWindowSize_newSize.plus(bufferedBytes).gt(2147483647))), method.is('initialWindowSizeChanged').implies(all(method.is('initialWindowSizeChanged').implies(all(initialWindowSizeChanged_delta.atLeast(-2147483648), initialWindowSizeChanged_delta.atMost(2147483647))), not(all(method.is('initialWindowSizeChanged'), initialWindowSizeChanged_delta.atLeast(-2147483648), initialWindowSizeChanged_delta.atMost(2147483647), any(targetWindowSize.plus(initialWindowSizeChanged_delta).lt(-2147483648), targetWindowSize.plus(initialWindowSizeChanged_delta).gt(2147483647)))))), method.is('bufferedFrameEmitted').implies(all(method.is('bufferedFrameEmitted').implies(bufferedBytes.minus(bufferedFrameEmitted_size).atLeast(0)), not(all(method.is('bufferedFrameEmitted'), bufferedBytes.minus(bufferedFrameEmitted_size).atLeast(0), not(lastWindowSize_none), not(closed), lastWindowSize.plus(bufferedBytes.minus(bufferedFrameEmitted_size)).lt(targetWindowSize), lastWindowSize.plus(bufferedBytes.minus(bufferedFrameEmitted_size)).atLeast(0), lastWindowSize.plus(bufferedBytes.minus(bufferedFrameEmitted_size)).gt(2147483647)))))))
  .step(({method, newWindowSize_newSize, lastWindowSize_none, lastWindowSize, initialWindowSizeChanged_delta, bufferedBytes, bufferedFrameReceived_size, bufferedFrameEmitted_size, targetWindowSize, closed}) => {
    const t1 = method.is('newWindowSize')
    const t2 = method.is('initialWindowSizeChanged')
    const t3 = lastWindowSize.plus(initialWindowSizeChanged_delta)
    const t4 = method.is('bufferedFrameReceived')
    const t5 = bufferedBytes.minus(bufferedFrameEmitted_size)
    const t6 = targetWindowSize.plus(initialWindowSizeChanged_delta)
    const t7 = newWindowSize_newSize.plus(bufferedBytes)
    const t8 = t7.atLeast(0)
    const t9 = t7.atMost(2147483647)
    const t10 = targetWindowSize.minus(t7)
    const t11 = t7.atMost(t10)
    const t12 = all(t8, t9, t11)
    const t13 = all(not(closed), t7.lt(targetWindowSize), any(t12, not(all(t8, t9, t10.lt(t7)))))
    const t14 = t3.plus(bufferedBytes)
    const t15 = t14.atLeast(0)
    const t16 = t6.minus(t14)
    const t17 = t14.atMost(t16)
    const t18 = all(t15, t17)
    const t19 = all(not(lastWindowSize_none), not(closed), t14.lt(t6), any(t18, t15.implies(t17)))
    const t20 = method.is('bufferedFrameEmitted')
    const t21 = lastWindowSize.plus(t5)
    const t22 = t21.atLeast(0)
    const t23 = t21.atMost(2147483647)
    const t24 = targetWindowSize.minus(t21)
    const t25 = t21.atMost(t24)
    const t26 = all(t22, t23, t25)
    const t27 = all(not(lastWindowSize_none), not(closed), t21.lt(targetWindowSize), any(t26, not(all(t22, t23, t24.lt(t21)))))
    return {lastWindowSize: when(t1, newWindowSize_newSize, when(t2, when(lastWindowSize_none, 0, t3), when(lastWindowSize_none, 0, lastWindowSize))), lastWindowSize_none: all(not(t1), lastWindowSize_none), bufferedBytes: when(t1, bufferedBytes, when(t2, bufferedBytes, when(t4, bufferedBytes.plus(bufferedFrameReceived_size), t5))), targetWindowSize: when(t1, targetWindowSize, when(t2, t6, targetWindowSize)), newWindowSize_result: when(t1, when(t13, when(t12, t10, when(t7.lt(0), t7.negate(), t7).plus(targetWindowSize).min(2147483647)), 0), 0), newWindowSize_result_none: all(t1, not(t13)), initialWindowSizeChanged_result: when(t1, 0, when(t2, when(t19, when(t18, t16, when(t14.lt(0), t14.negate(), t14).plus(t6).min(2147483647)), 0), 0)), initialWindowSizeChanged_result_none: all(t2, not(t19)), bufferedFrameEmitted_result: when(t1, 0, when(t2, 0, when(t4, 0, when(t20, when(t27, when(t26, t24, when(t21.lt(0), t21.negate(), t21).plus(targetWindowSize).min(2147483647)), 0), 0)))), bufferedFrameEmitted_result_none: all(t20, not(t27))}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const inboundWindowManagerInvariants = [inboundWindowManagerRule.law("targetWindowSize within its type's range", ({targetWindowSize}) => targetWindowSize.atMost(2147483647).and(targetWindowSize.atLeast(-2147483648))), inboundWindowManagerRule.law("lastWindowSize: a None one holds 0", ({lastWindowSize, lastWindowSize_none}) => any(lastWindowSize_none.not(), lastWindowSize.eq(0)))]
