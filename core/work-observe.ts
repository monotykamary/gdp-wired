// Untrusted search instrumentation; raw meter storage has no policy callback.
// New buckets are active only in raw-work-v1 full mode. Flags-off keeps every
// historical eval charge and leaves all six successor buckets zero.
import {coreMeter} from './meter.ts'
import {completeWorkProfile, type CompleteWorkKey} from './work-profile.ts'
import {runtimeWall} from './runtime-wall.ts'

type NativeKey = Extract<CompleteWorkKey, 'tinyNodes' | 'tinyTerms' | 'reachStates' | 'reachEdges' | 'reachEvals' | 'reachCompiledEvals'>
let reachDepth = 0
function charge(key: NativeKey, count: number): void {
  if (!completeWorkProfile.enabled) return
  if (!Number.isSafeInteger(count) || count < 0) throw new RangeError('native work count must be a nonnegative safe integer')
  runtimeWall.admit?.(completeWorkProfile.weights[key] * count, key)
  coreMeter[key] += count
}
export function tinyNode(): void { charge('tinyNodes', 1) }
let tinyCredit = 0
export function tinyTerm(): void {
  if (tinyCredit > 0) { tinyCredit--; coreMeter.tinyTerms++; return }
  charge('tinyTerms', 1)
}
// A closed generated tiny block has no loops, callbacks or other raw charges.
// Every emitted tick site executes at most once. Admit that upper bound once,
// charge only ticks actually visited, and discard unused credit on exit.
// Near the endpoint use per-tick admission instead of refusing the whole block.
export function tinyBlock<T>(maximum: number, run: () => T): T {
  if (!Number.isSafeInteger(maximum) || maximum < 0) throw new RangeError('tiny block requires a finite node bound')
  if (!completeWorkProfile.enabled || tinyCredit > 0) return run()
  if ((runtimeWall.remaining?.() ?? Infinity) < maximum * completeWorkProfile.weights.tinyTerms) return run()
  tinyCredit = maximum
  try { return run() } finally { tinyCredit = 0 }
}
export function reachState(): void { charge('reachStates', 1) }
export function reachEdge(): void { charge('reachEdges', 1) }
// Interpreted/closure operations count the actual visited expression nodes.
// Static compiled-step charges remain a separate bucket: their documented
// contract is one syntactic step-body node per invocation, not executed nodes.
export function observeEval(count = 1, compiled = false): void {
  if (!completeWorkProfile.enabled || !reachDepth) { coreMeter.evals += count; return }
  // The overwhelmingly common path is one actual expression-node visit.
  // Its count and coefficient are already validated; still admit every node.
  if (count === 1 && !compiled) {
    runtimeWall.admit?.(completeWorkProfile.weights.reachEvals, 'reachEvals')
    coreMeter.reachEvals += 1
  } else charge(compiled ? 'reachCompiledEvals' : 'reachEvals', count)
}
// Synchronous and nestable, with try/finally restoration; never a fresh budget.
export function withReachabilityWork<T>(run: () => T): T {
  if (!completeWorkProfile.enabled) return run()
  reachDepth++
  try { return run() } finally { reachDepth-- }
}
