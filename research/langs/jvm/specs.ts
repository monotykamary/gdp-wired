// Java and Kotlin projects' stateful classes, read by gdp-wired's JVM front ends (core/extract-jvm.ts): what each item
// reads, where its code is pinned, and the laws, written against the extracted rule's names. `run.ts` fetches each
// file (and the project's jar where the check runs the shipped classes) at its pin, extracts it (checked against the
// project's own code: compiled from the file with javac or kotlinc, or loaded from the release's jar, and run by
// core/jvm/Harness.java), and proves the laws; research/realworld/items/jvm-projects.ts scores the rules extracted at
// the pins with the corpus.
import {type Cond, type StepLaw, all, any} from '../../../core/dsl.ts'
import type {Law} from '../../../core/machine.ts'
import type {JvmOptions} from '../../../core/extract-jvm.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type X = any
type R = {stepLaw: (name: string, then: (b: X, a: X) => Cond, when?: (b: X) => Cond) => StepLaw, law: (name: string, f: (s: X) => Cond) => Law}
export type JvmLaw = {name: string, kind: 'step' | 'safety', intent: 'docs' | 'tests' | 'inferred', why: string, law: (r: R) => StepLaw | Law}
export type JvmSpec = {id: string, domain: 'rate limit' | 'circuit breaker', lang: 'java' | 'kotlin', project: string, version: string, licence: string, author: string, repo: string,
  // the files fetched (raw, at the tag) into the project's directory, the first the one read; the jars the check loads
  tag: string, root: string, files: string[], jars?: string[], reads: string, summary: string, opts: Omit<JvmOptions, 'root' | 'classpath' | 'javaHome' | 'kotlinHome'>, laws: JvmLaw[]}

const MAXI = 2147483647
const R4J = 'resilience4j-core/src/main/java/io/github/resilience4j/core/metrics'
export const SPECS: JvmSpec[] = [
  {id: 'rate limit/grpc-java/RetriableStream.Throttle', domain: 'rate limit', lang: 'java', project: 'grpc-java', version: '1.85.1', licence: 'Apache-2.0', author: 'The gRPC Authors', repo: 'grpc/grpc-java',
    tag: 'v1.85.1', root: 'core/src/main/java', files: ['core/src/main/java/io/grpc/internal/RetriableStream.java'], jars: ['io/grpc/grpc-core/1.85.1/grpc-core-1.85.1.jar'],
    reads: 'core/src/main/java/io/grpc/internal/RetriableStream.java: RetriableStream.Throttle (constructor, isAboveThreshold, onQualifiedFailureThenCheckIsAboveThreshold, onSuccess), checked against grpc-core-1.85.1.jar',
    summary: 'gRPC\'s retry throttling (the service config\'s retryThrottling): a token count, 1000 times the tokens, that starts at maxTokens, loses 1000 on each qualified failure (down to 0) and gains tokenRatio on each success (up to maxTokens); retries go on while it is above half of maxTokens. Each update a compare-and-set loop on an AtomicInteger.',
    opts: {entry: 'Throttle', prebuilt: true, methods: ['isAboveThreshold', 'onQualifiedFailureThenCheckIsAboveThreshold', 'onSuccess']},
    laws: [
      {name: 'the token count is always between 0 and maxTokens', kind: 'safety', intent: 'docs', why: 'RetriableStream.java: "The number of tokens starts at maxTokens. The token_count will always be between 0 and maxTokens."',
        law: r => r.law('the token count is always between 0 and maxTokens', s => any(s.maxTokens.lt(0), s.tokenRatio.lt(0), all(s.tokenCount.atLeast(0), s.tokenCount.atMost(s.maxTokens))))},
      {name: 'within gRPC\'s bounds the token count is always between 0 and maxTokens', kind: 'safety', intent: 'docs', why: 'the same comment, for a config ServiceConfigUtil accepts and a token ratio of at most 1000 (maxTokens is at most 1000: both at most 10^6 here)',
        law: r => r.law('within gRPC\'s bounds the token count is always between 0 and maxTokens', s => any(s.maxTokens.lt(0), s.maxTokens.gt(1_000_000), s.tokenRatio.lt(0), s.tokenRatio.gt(1_000_000), all(s.tokenCount.atLeast(0), s.tokenCount.atMost(s.maxTokens))))},
      {name: 'a qualified failure takes 1000 tokens, down to 0', kind: 'step', intent: 'docs', why: '"Counts down the token on qualified failure": Math.max(currentCount - 1000, 0)',
        law: r => r.stepLaw('a qualified failure takes 1000 tokens, down to 0', (b, a) => any(all(b.tokenCount.atLeast(1000), a.tokenCount.eq(b.tokenCount.minus(1000))), all(b.tokenCount.lt(1000), a.tokenCount.eq(0))), b => all(b.method.is('onQualifiedFailureThenCheckIsAboveThreshold'), b.tokenCount.atLeast(0)))},
      {name: 'isAboveThreshold is whether the count is above half of maxTokens', kind: 'step', intent: 'docs', why: 'threshold is "Half of maxTokens"; isAboveThreshold: tokenCount.get() > threshold',
        law: r => r.stepLaw('isAboveThreshold is whether the count is above half of maxTokens', (b, a) => a.isAboveThreshold_result.iff(b.tokenCount.gt(b.threshold)), b => b.method.is('isAboveThreshold'))},
      {name: 'the threshold is half of maxTokens', kind: 'safety', intent: 'docs', why: '"this.threshold = this.maxTokens / 2" (never written again)',
        law: r => r.law('the threshold is half of maxTokens', s => any(s.maxTokens.lt(0), all(s.threshold.times(2).atMost(s.maxTokens), s.maxTokens.lt(s.threshold.times(2).plus(2)))))},
    ]},
  {id: 'circuit breaker/resilience4j/PartialAggregation', domain: 'circuit breaker', lang: 'java', project: 'resilience4j', version: '2.4.0', licence: 'Apache-2.0', author: 'Robert Winkler and Bohdan Storozhuk', repo: 'resilience4j/resilience4j',
    tag: 'v2.4.0', root: 'resilience4j-core/src/main/java',
    files: ['PartialAggregation', 'AbstractAggregation', 'CumulativeMeasurement', 'Measurement', 'MeasurementData', 'Metrics', 'Snapshot', 'SnapshotImpl', 'TotalAggregation', 'PackedAggregation', 'FixedSizeSlidingWindowMetrics', 'SlidingTimeWindowMetrics', 'LockFreeFixedSizeSlidingWindowMetrics', 'LockFreeSlidingTimeWindowMetrics', 'MetricsPublisher'].map(f => `${R4J}/${f}.java`),
    reads: `${R4J}/PartialAggregation.java (and AbstractAggregation.java, its superclass): PartialAggregation(epochSecond), record(duration, durationUnit, outcome), reset(epochSecond)`,
    summary: 'One bucket of resilience4j\'s sliding time window (the circuit breaker\'s metrics): the number of calls, slow calls, failed calls and slow failed calls, and the total duration in milliseconds, by the outcome each call records (a switch on Metrics.Outcome that falls through); reset starts a new epoch second at 0.',
    opts: {entry: 'PartialAggregation', methods: ['record', 'reset']},
    laws: [
      {name: 'record counts one call', kind: 'step', intent: 'docs', why: 'AbstractAggregation.record: "this.numberOfCalls++"',
        law: r => r.stepLaw('record counts one call', (b, a) => a.numberOfCalls.eq(b.numberOfCalls.plus(1)), b => all(b.method.is('record'), b.numberOfCalls.lt(MAXI)))},
      {name: 'a slow error is slow, failed and slow failed', kind: 'step', intent: 'docs', why: 'case SLOW_ERROR: numberOfSlowCalls++; numberOfFailedCalls++; numberOfSlowFailedCalls++',
        law: r => r.stepLaw('a slow error is slow, failed and slow failed', (b, a) => all(a.numberOfSlowCalls.eq(b.numberOfSlowCalls.plus(1)), a.numberOfFailedCalls.eq(b.numberOfFailedCalls.plus(1)), a.numberOfSlowFailedCalls.eq(b.numberOfSlowFailedCalls.plus(1))),
          b => all(b.method.is('record'), b.record_outcome.is('SLOW_ERROR'), b.numberOfSlowCalls.lt(MAXI), b.numberOfFailedCalls.lt(MAXI), b.numberOfSlowFailedCalls.lt(MAXI)))},
      {name: 'a success counts nothing but the call', kind: 'step', intent: 'docs', why: 'record\'s switch has no case for SUCCESS (default: break)',
        law: r => r.stepLaw('a success counts nothing but the call', (b, a) => all(a.numberOfSlowCalls.eq(b.numberOfSlowCalls), a.numberOfFailedCalls.eq(b.numberOfFailedCalls), a.numberOfSlowFailedCalls.eq(b.numberOfSlowFailedCalls)), b => all(b.method.is('record'), b.record_outcome.is('SUCCESS')))},
      {name: 'record adds a millisecond duration as it is', kind: 'step', intent: 'docs', why: 'this.totalDurationInMillis += durationUnit.toMillis(duration)',
        law: r => r.stepLaw('record adds a millisecond duration as it is', (b, a) => a.totalDurationInMillis.eq(b.totalDurationInMillis.plus(b.record_duration)), b => all(b.method.is('record'), b.record_durationUnit.is('MILLISECONDS')))},
      {name: 'reset zeroes every count and starts the epoch', kind: 'step', intent: 'docs', why: 'PartialAggregation.reset: epochSecond set, totalDurationInMillis and the four counts 0',
        law: r => r.stepLaw('reset zeroes every count and starts the epoch', (b, a) => all(a.epochSecond.eq(b.reset_epochSecond), a.totalDurationInMillis.eq(0), a.numberOfCalls.eq(0), a.numberOfSlowCalls.eq(0), a.numberOfFailedCalls.eq(0), a.numberOfSlowFailedCalls.eq(0)), b => b.method.is('reset'))},
      {name: 'slow failed calls never outnumber slow calls', kind: 'safety', intent: 'inferred', why: 'every SLOW_ERROR counts both, SLOW_SUCCESS only the slow ones (the int counts wrap past MAX_VALUE)',
        law: r => r.law('slow failed calls never outnumber slow calls', s => s.numberOfSlowFailedCalls.atMost(s.numberOfSlowCalls))},
    ]},
  {id: 'rate limit/okhttp/WindowCounter', domain: 'rate limit', lang: 'kotlin', project: 'okhttp', version: '5.5.1', licence: 'Apache-2.0', author: 'Square, Inc.', repo: 'square/okhttp',
    tag: 'parent-5.5.1', root: 'okhttp/src/commonJvmAndroid/kotlin/okhttp3/internal/http2/flowcontrol', files: ['okhttp/src/commonJvmAndroid/kotlin/okhttp3/internal/http2/flowcontrol/WindowCounter.kt'],
    reads: 'okhttp/src/commonJvmAndroid/kotlin/okhttp3/internal/http2/flowcontrol/WindowCounter.kt: WindowCounter(streamId), update(total, acknowledged), unacknowledged',
    summary: 'OkHttp\'s HTTP/2 flow-control window count for a stream: the bytes consumed and the bytes acknowledged by WINDOW_UPDATE frames, each update adding to both under @Synchronized and checking both are non-negative and that no more is acknowledged than consumed.',
    opts: {entry: 'WindowCounter', methods: ['update', 'unacknowledged'], failures: 'kept'},
    laws: [
      {name: 'no more is acknowledged than consumed', kind: 'safety', intent: 'docs', why: 'update: "check(this.acknowledged <= this.total)"',
        law: r => r.law('no more is acknowledged than consumed', s => s.acknowledged.atMost(s.total))},
      {name: 'the counts never go below 0', kind: 'safety', intent: 'docs', why: 'update: "check(total >= 0)" and "check(acknowledged >= 0)" before either is added',
        law: r => r.law('the counts never go below 0', s => all(s.total.atLeast(0), s.acknowledged.atLeast(0)))},
      {name: 'an update within the window adds to both', kind: 'step', intent: 'docs', why: 'this.total += total; this.acknowledged += acknowledged',
        law: r => r.stepLaw('an update within the window adds to both', (b, a) => all(a.failed.not(), a.total.eq(b.total.plus(b.update_total)), a.acknowledged.eq(b.acknowledged.plus(b.update_acknowledged))),
          b => all(b.method.is('update'), b.update_total.atLeast(0), b.update_acknowledged.atLeast(0), b.acknowledged.plus(b.update_acknowledged).atMost(b.total.plus(b.update_total))))},
      {name: 'a negative update fails and changes nothing', kind: 'step', intent: 'docs', why: 'check(total >= 0) and check(acknowledged >= 0) throw before anything is written',
        law: r => r.stepLaw('a negative update fails and changes nothing', (b, a) => all(a.failed, a.total.eq(b.total), a.acknowledged.eq(b.acknowledged)), b => all(b.method.is('update'), any(b.update_total.lt(0), b.update_acknowledged.lt(0))))},
      {name: 'unacknowledged is the bytes consumed less those acknowledged', kind: 'step', intent: 'docs', why: '"val unacknowledged: Long @Synchronized get() = total - acknowledged"',
        law: r => r.stepLaw('unacknowledged is the bytes consumed less those acknowledged', (b, a) => a.unacknowledged_result.eq(b.total.minus(b.acknowledged)), b => b.method.is('unacknowledged'))},
    ]},
  {id: 'circuit breaker/arrow/OpeningStrategy.Count', domain: 'circuit breaker', lang: 'kotlin', project: 'arrow', version: '2.3.0.1', licence: 'Apache-2.0', author: 'The Arrow Authors', repo: 'arrow-kt/arrow',
    tag: '2.3.0.1', root: 'arrow-libs/resilience/arrow-resilience/src/commonMain/kotlin/arrow/resilience', files: ['arrow-libs/resilience/arrow-resilience/src/commonMain/kotlin/arrow/resilience/CircuitBreaker.kt'], jars: ['io/arrow-kt/arrow-resilience-jvm/2.3.0.1/arrow-resilience-jvm-2.3.0.1.jar', '$kotlin-stdlib'],
    reads: 'arrow-libs/resilience/arrow-resilience/src/commonMain/kotlin/arrow/resilience/CircuitBreaker.kt: CircuitBreaker.OpeningStrategy.Count (its init, shouldOpen, trackFailure, and OpeningStrategy.resetFailuresCount), checked against arrow-resilience-jvm-2.3.0.1.jar',
    summary: 'Arrow\'s count-based opening strategy for its CircuitBreaker: an immutable data class of the failures allowed and counted; trackFailure returns a copy counting one more, resetFailuresCount one at 0, shouldOpen is whether more failed than allowed. Each method that returns the next strategy is a step to it.',
    opts: {entry: 'OpeningStrategy.Count', prebuilt: true, methods: ['shouldOpen', 'trackFailure', 'resetFailuresCount']},
    laws: [
      {name: 'shouldOpen is whether more failed than allowed', kind: 'step', intent: 'docs', why: '"override fun shouldOpen(): Boolean = failuresCount > maxFailures"',
        law: r => r.stepLaw('shouldOpen is whether more failed than allowed', (b, a) => a.shouldOpen_result.iff(b.failuresCount.gt(b.maxFailures)), b => b.method.is('shouldOpen'))},
      {name: 'a tracked failure counts one more', kind: 'step', intent: 'docs', why: 'trackFailure: copy(failuresCount = failuresCount + 1)',
        law: r => r.stepLaw('a tracked failure counts one more', (b, a) => all(a.failuresCount.eq(b.failuresCount.plus(1)), a.maxFailures.eq(b.maxFailures)), b => all(b.method.is('trackFailure'), b.failuresCount.lt(MAXI)))},
      {name: 'a reset count is 0', kind: 'step', intent: 'docs', why: 'resetFailuresCount: "is Count -> copy(failuresCount = 0)"',
        law: r => r.stepLaw('a reset count is 0', (_b, a) => a.failuresCount.eq(0), b => b.method.is('resetFailuresCount'))},
      {name: 'the failures allowed are never below 0', kind: 'safety', intent: 'docs', why: 'init: "maxFailures expected to be greater than or equal to 0" (requireNotNull of takeIf { it >= 0 })',
        law: r => r.law('the failures allowed are never below 0', s => s.maxFailures.atLeast(0))},
    ]},
]
