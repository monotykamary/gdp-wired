// Research implementation switch. Off by default; these positive unit weights
// are a wiring fixture for lane I's raw counters, not D2's calibration or W.
// Freeze once so changing process.env cannot reprice an active proof.
export const completeWorkKeys = ['tableCells', 'checkSteps', 'astNodes', 'evals', 'cubeTests', 'ticks', 'cdclNodes', 'epr', 'tinyNodes', 'tinyTerms', 'reachStates', 'reachEdges', 'reachEvals', 'reachCompiledEvals'] as const
export type CompleteWorkKey = typeof completeWorkKeys[number]
export type CompleteWorkWeights = Readonly<Record<CompleteWorkKey, number>>
const environment = (globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env
const enabled = environment?.GDP_WORK_FULL === '1'
const weights = (() => {
  const supplied = enabled ? environment?.GDP_WORK_WEIGHTS : undefined
  const value: unknown = supplied === undefined ? Object.fromEntries(completeWorkKeys.map(key => [key, key === 'reachEvals' || key === 'reachCompiledEvals' ? 0.02 : 1])) : JSON.parse(supplied)
  if (!value || typeof value !== 'object' || Array.isArray(value)
    || Object.keys(value).length !== completeWorkKeys.length
    || completeWorkKeys.some(key => !Object.hasOwn(value, key) || typeof (value as Record<string, unknown>)[key] !== 'number'
      || !Number.isFinite((value as Record<string, number>)[key]) || (value as Record<string, number>)[key]! <= 0))
    throw new RangeError(`GDP_WORK_WEIGHTS requires exactly ${completeWorkKeys.length} positive finite raw-counter weights (raw-work-v1)`)
  return Object.freeze({...value}) as CompleteWorkWeights
})()
const configured = enabled ? environment?.GDP_WORK_W : undefined
const defaultUnits = configured === undefined ? 15_000_000 : Number(configured)
if (!Number.isFinite(defaultUnits) || defaultUnits < 0) throw new RangeError('GDP_WORK_W must be finite and nonnegative')
export const completeWorkProfile = Object.freeze({id: 'raw-work-v1', enabled, provisional: true as const, weights, defaultUnits})
