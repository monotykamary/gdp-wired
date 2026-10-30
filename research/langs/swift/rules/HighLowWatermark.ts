// backpressure/swift-nio/HighLowWatermark: extracted from swift-nio 2.104.0 (apple/swift-nio at 2.104.0), Sources/NIOCore/AsyncSequences/NIOAsyncSequenceProducerStrategies.swift: NIOAsyncSequenceProducerBackPressureStrategies.HighLowWatermark (init(lowWatermark:highWatermark:), didYield(bufferDepth:), didConsume(bufferDepth:)). Apache-2.0, (c) Apple Inc. and the SwiftNIO project authors.
// Extracted by gdp-wired/extract from NIOAsyncSequenceProducerStrategies.swift (HighLowWatermark, a class and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, any, bool, int, oneOf, rule, when} from '../../../../core/dsl.ts'

export const highLowWatermarkRule = rule("HighLowWatermark")
  .params({lowWatermark0: int, highWatermark0: int})
  .inputs({method: oneOf('didYield', 'didConsume'), didYield_bufferDepth: int, didConsume_bufferDepth: int})
  .state({hasOustandingDemand: bool.from(true), lowWatermark: int.from(({lowWatermark0}) => lowWatermark0), highWatermark: int.from(({highWatermark0}) => highWatermark0), didYield_result: bool.from(false), didConsume_result: bool.from(false)})
  .pre(({lowWatermark0, highWatermark0}) => lowWatermark0.atMost(highWatermark0))
  .step(({method, highWatermark, didYield_bufferDepth, hasOustandingDemand, didConsume_bufferDepth, lowWatermark}) => {
    const t1 = method.is('didYield')
    const t2 = didYield_bufferDepth.lt(highWatermark)
    const t3 = any(didConsume_bufferDepth.lt(lowWatermark), hasOustandingDemand)
    return {hasOustandingDemand: when(t1, all(t2, hasOustandingDemand), t3), didYield_result: all(t1, t2, hasOustandingDemand), didConsume_result: all(method.is('didConsume'), t3)}
  })
