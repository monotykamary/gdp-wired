import {Worker} from 'node:worker_threads'
import {hasFinite, walkOnce, type Law, type Machine} from '../../core/machine.ts'
import {runExactLean, sha256, type AggregateLeanReceipt} from './exact.ts'
import type {AggregateMechanism} from './assets.ts'
import type {SearchResult} from './worker.ts'

export type {AggregateLeanReceipt} from './exact.ts'
export type LeanAggregateOptions = Readonly<{searchMs?: number, leanMs?: number}>
export type LeanAggregateVerdict = Readonly<{
  kind: 'lean-checked'
  verdict: 'checked in Lean, not by the kernel'
  mechanism: AggregateMechanism
  receipt: AggregateLeanReceipt
}> | Readonly<{
  kind: 'not-checked'
  reason: 'unsupported' | 'search' | 'lean'
  detail: string
}>

function admissible(m: Machine, law: Law): boolean {
  // The exact literals here describe an ordinary natural-number SMachine, not
  // word failures, derived maps, external functions or alternative binders.
  if (m.primitiveFailure || m.history || m.counts || m.sums || m.inputMaps?.length || m.facts?.length ||
      Object.keys(m.fns ?? {}).length || Object.keys(m.leasts ?? {}).length || law.keys?.length || law.some?.length ||
      law.witness || law.ex || hasFinite([m, law]) || (law.stated && JSON.stringify(law.stated) !== JSON.stringify(law.holds))) return false
  if ((law.forall !== undefined && !law.forall) || [m.params, m.inputs].some(ns => ns.some(n => typeof n !== 'string'))) return false
  const nat = (v: unknown) => typeof v === 'number' && Number.isSafeInteger(v) && v >= 0
  const opcodes = new Set(['var', 'const', 'add', 'sub', 'min', 'max', 'mul', 'prod', 'if', 'get', 'tup', 'proj', '<', '<=', '=', 'and', 'or', 'not', 'flag'])
  const unsafe = /[\u0000-\u001f\u007f-\u009f\u2028\u2029]|\/-|-\//u
  let safe = Object.values(m.maps ?? {}).every(nat) && !unsafe.test(m.name) && !unsafe.test(law.name)
  walkOnce([m.state, m.step, m.pre, m.assume, law.holds], o => {
    const t = o as Record<string, unknown>
    const op = t.op
    if (typeof op === 'string' && (!opcodes.has(op) || op === 'const' && !nat(t.value) || op === 'mul' && !nat(t.k) ||
        op === 'proj' && t.k !== 0 && t.k !== 1 || op === 'get' && (typeof t.map !== 'string' || !Object.hasOwn(m.maps ?? {}, t.map)))) safe = false
  })
  // This exporter prints some source labels in comments. Never let a source
  // label break the comment boundary or supply Lean syntax.
  const names = [...m.params, ...m.inputs, ...Object.keys(m.state), ...Object.keys(m.maps ?? {}),
    ...Object.keys(m.step.state ?? {}), ...Object.keys(m.step.maps ?? {}), ...Object.keys(m.step.flags ?? {}), law.forall ?? '',
    ...Object.values(m.step.maps ?? {}).flatMap(w => 'each' in w ? [w.each] : [])]
  if (names.some(n => unsafe.test(n))) return false
  walkOnce([m.state, m.step, m.assume, m.pre, law.holds], o => {
    const t = o as Record<string, unknown>
    if ((t.op === 'var' || t.op === 'flag') && (typeof t.name !== 'string' || unsafe.test(t.name))) safe = false
  })
  return safe
}

async function search(input: {machine: Machine, law: Law, ms: number}): Promise<SearchResult> {
  const suffix = import.meta.url.endsWith('.ts') ? 'ts' : 'js'
  const worker = new Worker(new URL(`./worker.${suffix}`, import.meta.url), {workerData: input})
  let timer: ReturnType<typeof setTimeout> | undefined
  try {
    return await new Promise((resolve, reject) => {
      timer = setTimeout(() => reject(new Error('Aggregate search/serialization deadline expired.')), input.ms + 5000)
      worker.once('message', (result: SearchResult) => resolve(result))
      worker.once('error', reject)
      worker.once('exit', code => reject(new Error(`Aggregate worker exited without a candidate (${code}).`)))
    })
  } finally {
    clearTimeout(timer)
    if (worker.threadId !== -1) await worker.terminate()
  }
}

// Deliberately separate from proveRule/proveSteps and native verdict types.
// The only success branch is after exact Lean checking and axiom validation.
export async function proveLeanAggregate(machine: Machine, law: Law, options: LeanAggregateOptions = {}): Promise<LeanAggregateVerdict> {
  const {searchMs = 60_000, leanMs = 180_000} = options
  const budget = (ms: number, max: number) => Number.isSafeInteger(ms) && ms > 0 && ms <= max
  if (!budget(searchMs, 60_000) || !budget(leanMs, 600_000))
    return {kind: 'not-checked', reason: 'unsupported', detail: 'Use 1–60000 search ms and 1–600000 Lean ms.'}
  let input: string, result: SearchResult
  try {
    if (!admissible(machine, law)) return {kind: 'not-checked', reason: 'unsupported', detail: 'Unsupported source machine or invariant.'}
    input = JSON.stringify([machine, law])
    const [m, l] = JSON.parse(input) as [Machine, Law]
    if (!admissible(m, l) || JSON.stringify([m, l]) !== input) throw new Error('Source is not a supported serializable rule.')
    result = await search({machine: m, law: l, ms: searchMs})
  } catch (e) { return {kind: 'not-checked', reason: 'search', detail: String(e)} }
  if (result.kind === 'refused') return {kind: 'not-checked', reason: result.reason, detail: result.detail}
  try {
    const receipt = await runExactLean(result.mechanism, result.source, sha256(input), leanMs)
    return {kind: 'lean-checked', verdict: 'checked in Lean, not by the kernel', mechanism: result.mechanism, receipt}
  } catch (e) { return {kind: 'not-checked', reason: 'lean', detail: String(e)} }
}
