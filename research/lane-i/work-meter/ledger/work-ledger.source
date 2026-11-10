import {traceNow} from './trace-clock.ts'
import {completeWorkWeights, fullWork, rawWork, workKeys, type ExtraWorkWeights, type RawWork} from './work-meter.ts'

export type WorkPhase = Readonly<{
  id: number, parentId: number | null, name: string, depth: number, completed: boolean,
  raw: Readonly<RawWork>, exclusiveRaw: Readonly<RawWork>, units: number, exclusiveUnits: number,
  wallMs: number, exclusiveWallMs: number, unitModel: 'legacy' | 'explicit-complete', weights?: ExtraWorkWeights,
}>
type Frame = {id: number, name: string, children: RawWork, childUnits: number, childWall: number}
type Observer = {emit: (phase: WorkPhase) => void, stack: Frame[], nextId: number, errors: unknown[]}
let observer: Observer | undefined
const zero = (): RawWork => Object.fromEntries(workKeys.map(key => [key, 0])) as RawWork
const minus = (a: Readonly<RawWork>, b: Readonly<RawWork>): RawWork => Object.fromEntries(workKeys.map(key => [key, a[key] - b[key]])) as RawWork

// Synchronous diagnostics only. No counter is reset, charged, used as a stop,
// or summed a second time. The root is one end-minus-start observation;
// nested phases are inclusive, with separately reported exclusive deltas.
export function workPhase<T>(name: string, run: () => T): T {
  const active = observer
  if (!active) return run()
  const parent = active.stack.at(-1), frame: Frame = {id: active.nextId++, name, children: zero(), childUnits: 0, childWall: 0}
  const start = rawWork(), units = fullWork(), wall = traceNow(), weights = completeWorkWeights()
  const depth = active.stack.length
  active.stack.push(frame)
  let completed = false
  try { const result = run(); completed = true; return result }
  finally {
    const wallMs = traceNow() - wall, delta = minus(rawWork(), start), spent = fullWork() - units
    active.stack.pop()
    if (parent) {
      for (const key of workKeys) parent.children[key] += delta[key]
      parent.childUnits += spent; parent.childWall += wallMs
    }
    const event: WorkPhase = Object.freeze({id: frame.id, parentId: parent?.id ?? null, name, depth, completed,
      raw: Object.freeze(delta), exclusiveRaw: Object.freeze(minus(delta, frame.children)), units: spent,
      exclusiveUnits: spent - frame.childUnits, wallMs, exclusiveWallMs: wallMs - frame.childWall,
      unitModel: weights ? 'explicit-complete' : 'legacy', ...(weights ? {weights} : {})})
    // Broken output must not turn an accepted proof into a refusal or mask an error.
    try { active.emit(event) } catch (error) { active.errors.push(error) }
  }
}
export function withWorkLedger<T>(name: string, emit: (phase: WorkPhase) => void, run: () => T): T {
  if (observer) return workPhase(name, run)
  observer = {emit, stack: [], nextId: 1, errors: []}
  try { return workPhase(name, run) } finally { observer = undefined }
}
