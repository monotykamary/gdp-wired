// All full-work observations use the common exact bank. Old callback credits
// remain a compatibility surface only; they cannot authorize or charge work.
import {coreMeter} from './meter.ts'
import {completeWorkProfile, type CompleteWorkKey} from './work-profile.ts'
import {startWork} from './work-admission.ts'
type NativeKey = Extract<CompleteWorkKey, 'tinyNodes' | 'tinyTerms' | 'reachStates' | 'reachEdges' | 'reachEvals' | 'reachCompiledEvals'>
let reachDepth = 0
export const evaluationAdmissionHook: {admit?: (count: number) => void, invalidate?: () => void} = {}
export function withEvaluationAdmission<T>(run: () => T): T { return run() }
function charge(key: NativeKey, count: number): void { if (completeWorkProfile.enabled) startWork(key, count, key) }
export function tinyNode(): void { charge('tinyNodes', 1) }
export function tinyTerm(): void { charge('tinyTerms', 1) }
// Each actual visited site takes its own exact allowance. There is no separate
// maximum-sized bank, and an unvisited branch consumes nothing.
export function tinyBlock<T>(maximum: number, run: () => T): T {
  if (!Number.isSafeInteger(maximum) || maximum < 0) throw new RangeError('tiny block requires a finite node bound')
  return run()
}
export function reachState(): void { charge('reachStates', 1) }
export function reachEdge(): void { charge('reachEdges', 1) }
export function observeEval(count = 1, compiled = false): void {
  if (!completeWorkProfile.enabled) { coreMeter.evals += count; return }
  startWork(reachDepth ? compiled ? 'reachCompiledEvals' : 'reachEvals' : 'evals', count, compiled ? 'compiled step expression nodes' : 'expression node visit')
}
export function withReachabilityWork<T>(run: () => T): T {
  if (!completeWorkProfile.enabled) return run()
  reachDepth++
  try { return run() } finally { reachDepth-- }
}
