// This worker is used only by the opt-in API. A fresh worker-local kernel
// term table and emitter memo keep aggregate search separate from native calls.
import {parentPort, workerData} from 'node:worker_threads'
import type {Law, Machine} from '../../core/machine.ts'
import {searchWall} from '../../core/wall.ts'
import {withWall} from '../../kernel/prove.ts'
import type {AggregateMechanism} from './assets.ts'
import {foldTheory, provePointFold} from './point-fold.ts'
import {emitPointFold} from './replay-fold.ts'
import {emitWeighted} from './weighted-replay.ts'
import {weightedCandidates} from './weighted.ts'
import {closeWeightedFlags} from './weighted-flags.ts'
import {proveWeightedSeeded} from './weighted-seeded.ts'

export type SearchResult = {kind: 'candidate', mechanism: AggregateMechanism, source: string}
  | {kind: 'refused', reason: 'unsupported' | 'search', detail: string}

function propose(machine: Machine, law: Law, ms: number): SearchResult {
  if (foldTheory(machine, law)) {
    const packet = provePointFold(machine, law, Math.min(4000, ms))
    if (packet) return {kind: 'candidate', mechanism: 'finite-fold', source: emitPointFold(packet)}
  } else if (law.forall) {
    const candidates = weightedCandidates(machine, law).flatMap(p => closeWeightedFlags(p) ?? [])
    if (candidates.length) {
      const result = withWall(searchWall(Math.min(ms, 59_000)), () => {
        for (const candidate of candidates) {
          const v = proveWeightedSeeded(candidate, Math.min(ms, 58_000), () => {})
          if (v.proven && v.checked && v.proof) return emitWeighted(candidate, machine, law, v.proof)
        }
        return undefined
      })
      if (result) return {kind: 'candidate', mechanism: 'weighted', source: result}
      return {kind: 'refused', reason: 'search', detail: 'Weighted equality did not close.'}
    }
    return {kind: 'refused', reason: 'unsupported', detail: 'No weighted update shape recognized.'}
  } else return {kind: 'refused', reason: 'unsupported', detail: 'No finite-fold update shape recognized.'}
  return {kind: 'refused', reason: 'search', detail: 'Finite-fold local goals did not close.'}
}

const {machine, law, ms} = workerData as {machine: Machine, law: Law, ms: number}
try { parentPort!.postMessage(propose(machine, law, ms)) }
catch (e) { parentPort!.postMessage({kind: 'refused', reason: 'search', detail: String(e)} satisfies SearchResult) }
