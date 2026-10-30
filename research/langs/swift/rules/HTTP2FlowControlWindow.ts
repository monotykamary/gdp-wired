// flow control/swift-nio-http2/HTTP2FlowControlWindow: extracted from swift-nio-http2 1.46.0 (apple/swift-nio-http2 at 1.46.0), Sources/NIOHTTP2/HTTP2FlowControlWindow.swift: HTTP2FlowControlWindow (init(initialValue: Int), windowUpdate(by:), initialSizeChanged(by:), consume(flowControlledBytes:)). Apache-2.0, (c) Apple Inc. and the SwiftNIO project authors.
// Extracted by gdp-wired/extract from HTTP2FlowControlWindow.swift (HTTP2FlowControlWindow, a class and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, any, bool, int, Int, nat, oneOf, rule, when} from '../../../../core/dsl.ts'

export const hTTP2FlowControlWindowRule = rule("HTTP2FlowControlWindow")
  .params({initialValue: nat})
  .inputs({method: oneOf('windowUpdate', 'initialSizeChanged', 'consume'), windowUpdate_amount: nat, initialSizeChanged_amount: int, consume_size: int})
  .state({windowSize: int.from(({initialValue}) => initialValue), failed: bool.from(false)})
  .pre(({initialValue}) => all(initialValue.atLeast(0), initialValue.atLeast(0).implies(initialValue.atMost(2147483647))))
  .assume(({method, windowUpdate_amount, initialSizeChanged_amount}) => all(method.is('windowUpdate').implies(windowUpdate_amount.atMost(4294967295)), method.is('windowUpdate').implies(windowUpdate_amount.atLeast(0)), method.is('initialSizeChanged').implies(initialSizeChanged_amount.atMost(2147483647)), method.is('initialSizeChanged').implies(initialSizeChanged_amount.atLeast(-2147483648))))
  .step(({method, windowUpdate_amount, windowSize, initialSizeChanged_amount, consume_size}) => {
    const t1 = method.is('windowUpdate')
    const t2 = windowUpdate_amount.atMost(2147483647)
    const t3 = windowUpdate_amount.atLeast(1)
    const t4 = windowSize.lt(0)
    const t5 = Int.of(2147483647).minus(windowSize)
    const t6 = Int.of(windowUpdate_amount).atMost(t5)
    const t7 = any(t4, t6)
    const t8 = windowSize.plus(windowUpdate_amount)
    const t9 = t8.gt(2147483647)
    const t10 = method.is('initialSizeChanged')
    const t11 = initialSizeChanged_amount.atLeast(-2147483647)
    const t12 = initialSizeChanged_amount.atMost(t5)
    const t13 = any(t4, t12)
    const t14 = windowSize.plus(initialSizeChanged_amount)
    const t15 = t14.lt(-2147483648)
    const t16 = t14.gt(2147483647)
    const t17 = consume_size.atLeast(0)
    const t18 = consume_size.atMost(16777215)
    const t19 = consume_size.atMost(windowSize)
    const t20 = windowSize.atLeast(0)
    const t21 = method.is('consume')
    return {windowSize: when(t1, when(all(t2, t3, t7, t8.atMost(2147483647)), t8, windowSize), when(t10, when(all(t11, t13, t14.atLeast(-2147483648), t14.atMost(2147483647)), t14, windowSize), when(all(t17, t18, t19), windowSize.minus(consume_size), windowSize))), failed: any(all(t1, any(all(t1, windowUpdate_amount.gt(2147483647)), all(t1, t2, windowUpdate_amount.lt(1)), all(t1, t2, t3, t20, t5.lt(windowUpdate_amount)), all(t1, t2, t3, t7, t9))), all(t10, any(all(t10, initialSizeChanged_amount.lt(-2147483647)), all(t10, t11, t20, t5.lt(initialSizeChanged_amount)), all(t10, t11, t13, any(t15, t16)))), all(t21, any(all(t21, consume_size.lt(0)), all(t21, t17, consume_size.gt(16777215)), all(t21, t17, t18, windowSize.lt(consume_size)))))}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const hTTP2FlowControlWindowInvariants = [hTTP2FlowControlWindowRule.law("windowSize within its type's range", ({windowSize}) => windowSize.atMost(2147483647).and(windowSize.atLeast(-2147483648)))]
