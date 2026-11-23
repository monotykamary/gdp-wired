import { createHash } from 'node:crypto'

// A canonical job of supercomputer/suite.json, and the hash of its whole definition: a known failure
// (known-failures.json) is bound to the definition it was observed on, so a changed job is never excused by an old
// entry. (Moved unchanged from the retired full-gate-contract.ts: existing entries' definitionSha256 stay valid.)
export type CanonicalJob = { name: string; cmd: string; [key: string]: unknown }

const fail = (message: string): never => { throw new Error(`full-gate: ${message}`) }
const object = (v: unknown, label: string): Record<string, unknown> => {
  if (v === null || typeof v !== 'object' || Array.isArray(v) || ![Object.prototype, null].includes(Object.getPrototypeOf(v))) return fail(`${label} must be an object`)
  return v as Record<string, unknown>
}
const text = (v: unknown, label: string): string => {
  if (typeof v !== 'string' || !v.trim() || v !== v.trim()) return fail(`${label} must be a nonempty trimmed string`)
  return v
}

// Stable JSON: recursively sorted object keys, original array order, no lossy
// JSON coercions. Hashes the entire definition, not just its command/name.
function stableJson(v: unknown, ancestors = new Set<object>()): string {
  if (v === null || typeof v === 'string' || typeof v === 'boolean') return JSON.stringify(v)
  if (typeof v === 'number' && Number.isFinite(v)) return JSON.stringify(v)
  if (typeof v !== 'object' || v === null || ancestors.has(v)) return fail('canonical job is not JSON data')
  ancestors.add(v)
  let result: string
  if (Array.isArray(v)) {
    if (Object.keys(v).length !== v.length) return fail('canonical job contains a sparse or decorated array')
    result = '[' + v.map(x => stableJson(x, ancestors)).join(',') + ']'
  } else {
    const o = object(v, 'canonical job value')
    if (Object.getOwnPropertySymbols(o).length) return fail('canonical job has symbol keys')
    result = '{' + Object.keys(o).sort().map(k => JSON.stringify(k) + ':' + stableJson(o[k], ancestors)).join(',') + '}'
  }
  ancestors.delete(v)
  return result
}

export function canonicalJobHash(job: CanonicalJob): string {
  object(job, 'canonical job')
  text(job.name, 'canonical job name'); text(job.cmd, 'canonical job cmd')
  return createHash('sha256').update(stableJson(job), 'utf8').digest('hex')
}
