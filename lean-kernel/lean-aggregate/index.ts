import {Worker} from 'node:worker_threads'
import type {Law, Machine} from '../../core/machine.ts'
import {admitAggregateSource} from './source.ts'
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

async function search(input: {source: string, ms: number}): Promise<SearchResult> {
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
  let input: string
  try { input = admitAggregateSource(machine, law) }
  catch (e) { return {kind: 'not-checked', reason: 'unsupported', detail: String(e)} }
  let result: SearchResult
  try { result = await search({source: input, ms: searchMs}) }
  catch (e) { return {kind: 'not-checked', reason: 'search', detail: String(e)} }
  if (result.kind === 'refused') return {kind: 'not-checked', reason: result.reason, detail: result.detail}
  try {
    const receipt = await runExactLean(result.mechanism, result.source, sha256(input), leanMs)
    return {kind: 'lean-checked', verdict: 'checked in Lean, not by the kernel', mechanism: result.mechanism, receipt}
  } catch (e) { return {kind: 'not-checked', reason: 'lean', detail: String(e)} }
}
