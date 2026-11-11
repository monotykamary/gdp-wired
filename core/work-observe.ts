// Untrusted search instrumentation; raw meter storage has no policy callback.
// New buckets are active only in raw-work-v1 full mode. Flags-off keeps every
// historical eval charge and leaves all six successor buckets zero.
import {coreMeter} from './meter.ts'
import {completeWorkProfile, type CompleteWorkKey} from './work-profile.ts'
import {runtimeWall} from './runtime-wall.ts'

type NativeKey = Extract<CompleteWorkKey, 'tinyNodes' | 'tinyTerms' | 'reachStates' | 'reachEdges' | 'reachEvals' | 'reachCompiledEvals'>
let reachDepth = 0
let evaluationDepth = 0, evaluationCredit = 0
// Keep the interpreter's import leaf dependency-free. Rich search scopes install
// the guarded amortizer; isolated model interpretation retains its small block.
export const evaluationAdmissionHook: {admit?: (count: number) => void, invalidate?: () => void} = {}
function admitEvaluation(count: number): void {
  if (count !== 1 && (!Number.isSafeInteger(count) || count < 0)) throw new RangeError('invalid evaluation count')
  if (evaluationCredit < count) {
    const weight = completeWorkProfile.weights.evals
    const block = Math.max(count, Math.max(1, Math.min(256, Math.floor(256 / weight))))
    const units = block * weight
    if (Number.isFinite(units) && (runtimeWall.remaining?.() ?? Infinity) >= units) {
      runtimeWall.admit?.(units, 'model evaluations'); evaluationCredit = block
    } else {
      runtimeWall.admit?.(count * weight, 'model evaluations'); evaluationCredit = count
    }
  }
  evaluationCredit -= count
}
export function withEvaluationAdmission<T>(run: () => T): T {
  if (!completeWorkProfile.enabled) return run()
  const priorAdmit = runtimeWall.admit
  runtimeWall.admit = (units, phase) => { evaluationCredit = 0; priorAdmit?.(units, phase) }
  evaluationDepth++; evaluationCredit = 0
  try { return run() } finally { evaluationDepth--; evaluationCredit = 0; runtimeWall.admit = priorAdmit }
}

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
  if (!completeWorkProfile.enabled || !reachDepth) {
    if (completeWorkProfile.enabled) {
      if (evaluationAdmissionHook.admit) evaluationAdmissionHook.admit(count)
      else if (evaluationDepth) admitEvaluation(count)
      else runtimeWall.admit?.(count * completeWorkProfile.weights.evals, 'model evaluations')
    }
    coreMeter.evals += count; return
  }
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
