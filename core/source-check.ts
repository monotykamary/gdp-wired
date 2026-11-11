// Source proofs are proofs of translated rules. Keep their native observations outside the
// symbolic rule and outside serialized evidence, and require a native-law check at finalization.
// This module has no extractor/TypeScript dependency: ordinary builder proofs stay unchanged.
export type Translation = 'exhaustive' | 'sampled' | 'unchecked' | 'error'
export type NativeObservation = {
  where: string, method?: string, before: unknown, after: unknown,
  params: Record<string, unknown>, inputs: Record<string, unknown>, bindings: Record<string, unknown>,
  args: unknown[], result: unknown, failed: boolean, legacyResult?: boolean,
}
export type NativeJournal = {
  enabled: boolean, complete: boolean, scope: 'exhaustive' | 'sampled', reason?: string,
  observations: NativeObservation[],
}
export type TranslationFields = {translation?: Translation, translationChecks?: number, translationWitness?: NativeObservation, kernelProven?: boolean}
// A non-enumerable, versioned marker survives independent module copies. Losing
// the private observations must downgrade a source proof, not turn it into a DSL proof.
const sourceMarker = Symbol.for('gdp-wired.source-proof.v1')
const marked = (value: object): boolean => Object.prototype.hasOwnProperty.call(value, sourceMarker)
const mark = (value: object, enumerable = false): void => { if (!marked(value)) Object.defineProperty(value, sourceMarker, {value: true, enumerable}) }
const markRule = (value: object): void => {
  mark(value)
  // A Rule's immutable specification is spread by constructor-based transforms.
  // Carry only the fail-closed marker, never a native journal, across such copies.
  const spec: unknown = Object.getOwnPropertyDescriptor(value, 'spec')?.value
  if (spec && typeof spec === 'object') mark(spec, true)
}
export function inheritSource(from: object, to: object, transparent = false): void {
  if (marked(from)) markRule(to)
  const source = sources.get(from)
  if (transparent && source) sources.set(to, source)
}
const evidence = new WeakMap<object, NativeJournal>()
const sources = new WeakMap<object, {root: object, journal?: NativeJournal, generated: Set<object>}>()
const nativeLaws = new WeakMap<object, {rule: object, method?: string, name: string, evaluate: (observation: NativeObservation) => boolean}>()
export function rememberNative(e: object, journal: NativeJournal): void { evidence.set(e, journal) }
export function attachSource(rule: object, e: object, generated: object[]): void {
  markRule(rule)
  sources.set(rule, {root: rule, journal: evidence.get(e), generated: new Set(generated)})
}
export function attachNativeLaw(rule: object, law: object, name: string, method: string | undefined, evaluate: (observation: NativeObservation) => boolean): void {
  mark(law)
  nativeLaws.set(law, {rule: sources.get(rule)?.root ?? rule, name, method, evaluate})
}
type TranslatedVerdict<V> = Omit<V, 'proven' | 'checked'> & {proven: boolean, checked: boolean} & TranslationFields
export function translationVerdict<V extends {proven: boolean, checked: boolean, why?: string, stuck?: string}>(rule: object, laws: object[], verdict: V): TranslatedVerdict<V> {
  const source = sources.get(rule), bound = laws.map(l => nativeLaws.get(l)).filter(x => x !== undefined)
  if (!source && !bound.length && !marked(rule) && !laws.some(marked)) return verdict
  const journal = source?.journal
  const unchecked = (why: string): TranslatedVerdict<V> => ({...verdict, proven: false, checked: false, kernelProven: verdict.proven && verdict.checked, translation: 'unchecked', why: `source translation unchecked: ${why}`})
  if (!journal?.enabled || !journal.complete) return unchecked(journal?.reason ?? 'native source replay is unavailable or disabled')
  if (bound.some(b => b.rule !== source?.root)) return unchecked('the source law belongs to a different rule')
  if (laws.some(l => !nativeLaws.has(l) && !source!.generated.has(l))) return unchecked('a source proof contains a law with no native interpretation')
  if (!verdict.proven || !verdict.checked) return {...verdict, translation: journal.scope}
  let checks = 0
  for (const law of bound) {
    let observed = 0
    for (const observation of journal.observations) {
      if (law.method && observation.method !== law.method) continue
      observed++; checks++
      let holds: boolean
      try { holds = law.evaluate(observation) }
      catch (e) { return unchecked(`native interpretation of ${law.name}: ${e instanceof Error ? e.message : String(e)}`) }
      if (!holds) return {...verdict, proven: false, checked: false, kernelProven: true, translation: 'error', translationChecks: checks,
        translationWitness: observation, stuck: 'translation-error', why: `translation error: ${law.name} is false in the native code (${observation.where})`}
    }
    if (!observed) return unchecked(`no native observation of ${law.method ?? law.name}`)
  }
  return {...verdict, translation: journal.scope, translationChecks: checks}
}
const sourceIdentity = new WeakMap<object, number>(), cloneIdentity = new WeakMap<object, number>()
let nextIdentity = 0
const identify = (original: object, clone: object) => {
  let id = sourceIdentity.get(original)
  if (id === undefined) { id = ++nextIdentity; sourceIdentity.set(original, id) }
  cloneIdentity.set(clone, id)
}
export const nativeSame = (a: unknown, b: unknown): boolean => a === b || (a !== null && b !== null && typeof a === 'object' && typeof b === 'object' && cloneIdentity.has(a) && cloneIdentity.get(a) === cloneIdentity.get(b))
// Snapshot real JS values, preserving undefined, NaN, keys, aliasing and class prototypes.
// Functions are not invoked; laws cannot introduce arbitrary calls. An unsupported snapshot
// must make source proof finalization unchecked, never silently lose an observation.
export function nativeSnapshot(value: unknown, seen = new Map<object, unknown>()): unknown {
  if (value === null || typeof value !== 'object') return value
  if (seen.has(value)) return seen.get(value)
  if (seen.size >= 10000) throw new Error('native state exceeds the snapshot bound')
  const tag = Object.prototype.toString.call(value)
  if (tag === '[object Date]') { const out = new Date(Number(value)); identify(value, out); return out }
  if (tag === '[object Map]') {
    const out = new Map<unknown, unknown>(); seen.set(value, out); identify(value, out)
    for (const [k, v] of (value as Map<unknown, unknown>).entries()) out.set(nativeSnapshot(k, seen), nativeSnapshot(v, seen))
    return out
  }
  if (tag === '[object Set]') {
    const out = new Set<unknown>(); seen.set(value, out); identify(value, out)
    for (const v of (value as Set<unknown>).values()) out.add(nativeSnapshot(v, seen))
    return out
  }
  const out = (Array.isArray(value) ? [] : Object.create(Object.getPrototypeOf(value))) as Record<PropertyKey, unknown>
  seen.set(value, out); identify(value, out)
  for (const key of Reflect.ownKeys(value)) {
    const d = Object.getOwnPropertyDescriptor(value, key)!
    if ('value' in d) Object.defineProperty(out, key, {...d, value: nativeSnapshot(d.value, seen)})
    else Object.defineProperty(out, key, d)
  }
  return out
}
