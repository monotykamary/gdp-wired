// Swift projects' stateful types, read by gdp-wired's Swift front end (core/extract-swift.ts): what each item reads,
// where its code is pinned, and the laws, written against the extracted rule's names. `run.ts` clones each package at
// its tag, extracts the type (checked against the package itself: built by `swift build` beside the generated harness,
// in debug, and run request by request), and proves the laws; research/realworld/items/swift-projects.ts scores the
// rules extracted at the pins with the corpus.
import {type Cond, type StepLaw, all, any} from '../../../core/dsl.ts'
import type {Law} from '../../../core/machine.ts'
import type {SwiftOptions} from '../../../core/extract-swift.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type X = any
type R = {stepLaw: (name: string, then: (b: X, a: X) => Cond, when?: (b: X) => Cond) => StepLaw, law: (name: string, f: (s: X) => Cond) => Law}
export type SwiftLaw = {name: string, kind: 'step' | 'safety', intent: 'docs' | 'tests' | 'inferred', why: string, law: (r: R) => StepLaw | Law}
export type SwiftSpec = {id: string, domain: 'rate limit' | 'queue', project: string, version: string, licence: string, author: string, repo: string, tag: string,
  // the file read (under the package's root), what it reads, and the options
  file: string, reads: string, summary: string, opts: Omit<SwiftOptions, 'swift'>, laws: SwiftLaw[]}

const I32 = 2147483647
const IWM = 'flow control/swift-nio-http2/InboundWindowManager', FCW = 'flow control/swift-nio-http2/HTTP2FlowControlWindow'
const H2 = {project: 'swift-nio-http2', version: '1.46.0', licence: 'Apache-2.0', author: 'Apple Inc. and the SwiftNIO project authors', repo: 'apple/swift-nio-http2', tag: '1.46.0'}
export const SPECS: SwiftSpec[] = [
  {id: IWM, domain: 'rate limit', ...H2, file: 'Sources/NIOHTTP2/InboundWindowManager.swift',
    reads: 'Sources/NIOHTTP2/InboundWindowManager.swift: InboundWindowManager (init(targetSize:), newWindowSize, initialWindowSizeChanged, bufferedFrameReceived, bufferedFrameEmitted, and calculateWindowIncrement inlined)',
    summary: 'SwiftNIO HTTP/2\'s inbound flow control: the window update to send (WINDOW_UPDATE\'s increment) when a stream\'s or the connection\'s window drops to half its target or below, counting the bytes of frames still buffered; a change of the initial window size moves the target; a closed window sends none. Int32 arithmetic that traps (Swift\'s default), Int32(x) conversions that trap, an Optional last window size.',
    opts: {entry: 'InboundWindowManager', methods: ['newWindowSize', 'initialWindowSizeChanged', 'bufferedFrameReceived', 'bufferedFrameEmitted']},
    laws: [
      {name: 'an increment fits a WINDOW_UPDATE (at most 2^31 - 1)', kind: 'step', intent: 'docs', why: '"increment by Int32.max or the total distance between newSize and targetWindowSize, whichever is *smaller*. This ensures the result fits into Int32."',
        law: r => r.stepLaw('an increment fits a WINDOW_UPDATE (at most 2^31 - 1)', (b, a) => all(b.method.is('newWindowSize').implies(any(a.newWindowSize_result_none, a.newWindowSize_result.atMost(I32))), b.method.is('initialWindowSizeChanged').implies(any(a.initialWindowSizeChanged_result_none, a.initialWindowSizeChanged_result.atMost(I32))), b.method.is('bufferedFrameEmitted').implies(any(a.bufferedFrameEmitted_result_none, a.bufferedFrameEmitted_result.atMost(I32)))))},
      {name: 'an increment is positive while the target is not negative', kind: 'step', intent: 'docs', why: 'a WINDOW_UPDATE\'s increment of 0 is a protocol error (RFC 9113 6.9); the target is the initial window size setting, never below 0',
        law: r => r.stepLaw('an increment is positive while the target is not negative', (b, a) => all(b.method.is('newWindowSize').implies(any(a.newWindowSize_result_none, a.newWindowSize_result.gt(0))), b.method.is('bufferedFrameEmitted').implies(any(a.bufferedFrameEmitted_result_none, a.bufferedFrameEmitted_result.gt(0)))), b => b.targetWindowSize.atLeast(0))},
      {name: 'a non-negative window is brought back to the target', kind: 'step', intent: 'docs', why: '"if targetWindowSize >= newSize * 2, we update to full size": the window plus its increment is the target',
        law: r => r.stepLaw('a non-negative window is brought back to the target', (b, a) => any(a.newWindowSize_result_none, a.newWindowSize_result.plus(b.newWindowSize_newSize).plus(b.bufferedBytes).eq(b.targetWindowSize)), b => all(b.method.is('newWindowSize'), b.newWindowSize_newSize.plus(b.bufferedBytes).atLeast(0)))},
      {name: 'an update only once the window is at half its target or below', kind: 'step', intent: 'docs', why: '"if targetWindowSize >= newSize * 2, we update to full size" (else none)',
        law: r => r.stepLaw('an update only once the window is at half its target or below', (b, a) => any(a.newWindowSize_result_none, b.newWindowSize_newSize.plus(b.bufferedBytes).times(2).atMost(b.targetWindowSize)), b => b.method.is('newWindowSize'))},
      {name: 'no update before a window size is known', kind: 'step', intent: 'docs', why: 'initialWindowSizeChanged and bufferedFrameEmitted return nil while lastWindowSize is nil',
        law: r => r.stepLaw('no update before a window size is known', (b, a) => all(b.method.is('initialWindowSizeChanged').implies(a.initialWindowSizeChanged_result_none), b.method.is('bufferedFrameEmitted').implies(a.bufferedFrameEmitted_result_none)), b => b.lastWindowSize_none)},
      {name: 'the buffered bytes are never negative', kind: 'safety', intent: 'inferred', why: 'bufferedFrameEmitted asserts it after subtracting (the debug build traps there); bufferedFrameReceived adds any size it is given',
        law: r => r.law('the buffered bytes are never negative', s => s.bufferedBytes.atLeast(0))},
    ]},
  {id: FCW, domain: 'rate limit', ...H2, file: 'Sources/NIOHTTP2/HTTP2FlowControlWindow.swift',
    reads: 'Sources/NIOHTTP2/HTTP2FlowControlWindow.swift: HTTP2FlowControlWindow (init(initialValue: Int), windowUpdate(by:), initialSizeChanged(by:), consume(flowControlledBytes:))',
    summary: 'SwiftNIO HTTP/2\'s flow control window (one per stream and per connection): a WINDOW_UPDATE raises it (an increment of 0, or one past 2^31 - 1, a protocol error thrown), a change of SETTINGS_INITIAL_WINDOW_SIZE moves it by the delta (it may go negative), and a DATA frame consumes it (more than it holds, a flow control error thrown). Int32 with Swift\'s overflow trap, failures kept as the result.',
    opts: {entry: 'HTTP2FlowControlWindow', ctor: '(initialValue: Int)', methods: ['windowUpdate', 'initialSizeChanged', 'consume'], failures: 'kept'},
    laws: [
      {name: 'a window update of 0 is an error', kind: 'step', intent: 'docs', why: '"Window increments may never be zero or negative" (RFC 9113 6.9): throws invalidWindowIncrementSize',
        law: r => r.stepLaw('a window update of 0 is an error', (_b, a) => a.failed, b => all(b.method.is('windowUpdate'), b.windowUpdate_amount.eq(0)))},
      {name: 'a window update never takes the window past 2^31 - 1', kind: 'step', intent: 'docs', why: '"We now need to bounds check to confirm that our window size will remain in the valid range"',
        law: r => r.stepLaw('a window update never takes the window past 2^31 - 1', (_b, a) => any(a.failed, a.windowSize.atMost(I32)), b => b.method.is('windowUpdate'))},
      {name: 'a window update past the maximum is an error', kind: 'step', intent: 'docs', why: 'throws invalidFlowControlWindowSize when the window would exceed maxSize (a non-negative window)',
        law: r => r.stepLaw('a window update past the maximum is an error', (_b, a) => a.failed, b => all(b.method.is('windowUpdate'), b.windowSize.atLeast(0), b.windowSize.plus(b.windowUpdate_amount).gt(I32)))},
      {name: 'consuming never takes a window below 0', kind: 'step', intent: 'docs', why: 'consume: "guard self.windowSize >= size else { throw NIOHTTP2Errors.flowControlViolation() }"',
        law: r => r.stepLaw('consuming never takes a window below 0', (_b, a) => any(a.failed, a.windowSize.atLeast(0)), b => all(b.method.is('consume'), b.consume_size.atLeast(0)))},
      {name: 'consuming more than the window holds is an error', kind: 'step', intent: 'docs', why: 'the same guard: a flow control violation',
        law: r => r.stepLaw('consuming more than the window holds is an error', (_b, a) => a.failed, b => all(b.method.is('consume'), b.consume_size.gt(b.windowSize)))},
      {name: 'a settings change from a window of 0 or more never fails', kind: 'step', intent: 'docs', why: 'initialSizeChanged\'s guard (the window stays within 2^31 - 1) and its assert (the delta at least -(2^31 - 1))',
        law: r => r.stepLaw('a settings change from a window of 0 or more never fails', (_b, a) => a.failed.not(), b => all(b.method.is('initialSizeChanged'), b.windowSize.atLeast(0), b.initialSizeChanged_amount.atLeast(-I32), b.windowSize.plus(b.initialSizeChanged_amount).atMost(I32)))},
      {name: 'a settings change never fails but past the maximum', kind: 'step', intent: 'inferred', why: 'initialSizeChanged throws only where the window would pass 2^31 - 1; a window already negative skips the guard, and its += traps where it would pass -2^31',
        law: r => r.stepLaw('a settings change never fails but past the maximum', (_b, a) => a.failed.not(), b => all(b.method.is('initialSizeChanged'), b.initialSizeChanged_amount.atLeast(-I32), b.windowSize.plus(b.initialSizeChanged_amount).atMost(I32)))},
    ]},
  {id: 'backpressure/swift-nio/HighLowWatermark', domain: 'queue', project: 'swift-nio', version: '2.104.0', licence: 'Apache-2.0', author: 'Apple Inc. and the SwiftNIO project authors', repo: 'apple/swift-nio', tag: '2.104.0',
    file: 'Sources/NIOCore/AsyncSequences/NIOAsyncSequenceProducerStrategies.swift',
    reads: 'Sources/NIOCore/AsyncSequences/NIOAsyncSequenceProducerStrategies.swift: NIOAsyncSequenceProducerBackPressureStrategies.HighLowWatermark (init(lowWatermark:highWatermark:), didYield(bufferDepth:), didConsume(bufferDepth:))',
    summary: 'SwiftNIO\'s default back-pressure strategy for NIOAsyncSequenceProducer: demand stops once the buffer reaches the high watermark and resumes once it falls below the low one (hysteresis between them).',
    opts: {entry: 'HighLowWatermark', methods: ['didYield', 'didConsume']},
    laws: [
      {name: 'a yield at the high watermark stops demand', kind: 'step', intent: 'docs', why: '"We are demanding more until we reach the high watermark"',
        law: r => r.stepLaw('a yield at the high watermark stops demand', (_b, a) => a.didYield_result.not(), b => all(b.method.is('didYield'), b.didYield_bufferDepth.atLeast(b.highWatermark)))},
      {name: 'a consume below the low watermark resumes demand', kind: 'step', intent: 'docs', why: '"We start demanding again once we are below the low watermark"',
        law: r => r.stepLaw('a consume below the low watermark resumes demand', (_b, a) => a.didConsume_result, b => all(b.method.is('didConsume'), b.didConsume_bufferDepth.lt(b.lowWatermark)))},
      {name: 'a yield never resumes demand', kind: 'step', intent: 'docs', why: 'didYield only ever sets hasOustandingDemand to false',
        law: r => r.stepLaw('a yield never resumes demand', (b, a) => a.hasOustandingDemand.implies(b.hasOustandingDemand), b => b.method.is('didYield'))},
      {name: 'a consume never stops demand', kind: 'step', intent: 'docs', why: 'didConsume only ever sets hasOustandingDemand to true',
        law: r => r.stepLaw('a consume never stops demand', (b, a) => b.hasOustandingDemand.implies(a.hasOustandingDemand), b => b.method.is('didConsume'))},
      {name: 'the result is the demand after the step', kind: 'step', intent: 'docs', why: 'both return self.hasOustandingDemand',
        law: r => r.stepLaw('the result is the demand after the step', (b, a) => all(b.method.is('didYield').implies(a.didYield_result.iff(a.hasOustandingDemand)), b.method.is('didConsume').implies(a.didConsume_result.iff(a.hasOustandingDemand))))},
      {name: 'the watermarks never cross', kind: 'safety', intent: 'docs', why: 'init: precondition(lowWatermark <= highWatermark); neither is written again',
        law: r => r.law('the watermarks never cross', s => s.lowWatermark.atMost(s.highWatermark))},
    ]},
]
