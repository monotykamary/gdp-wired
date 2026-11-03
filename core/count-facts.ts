// Untrusted, opt-in counting proposals. No hypothesis here is an axiom: callers
// pass insts to countedGoal/mcGoal, prove that goal, then checkCounted/checkMC.
// Venn regions are a search representation, NOT new declared count variables.
import {type C, type E, x} from './machine.ts'
import {type Count, type CountDecl, type CountInst, type MapRead, substE} from '../kernel/kernel.ts'

export type CountFactOptions = {
  maxAtoms?: number
  maxCounts?: number
  maxFacts?: number
  reserved?: Iterable<string>
}
export type CountRegions = {below: E, atoms: C[], counts: string[], rows: number[][]}
export type CountFacts = {
  insts: CountInst[]
  regions: CountRegions[]
  skipped: {count: string, reason: string}[]
}

const stable = (t: unknown): string => JSON.stringify(t, (_, v: unknown) => v && typeof v === 'object' && !Array.isArray(v)
  ? Object.fromEntries(Object.entries(v).sort(([a], [b]) => a.localeCompare(b))) : v)
const namesIn = (t: unknown, out = new Set<string>()): Set<string> => {
  if (typeof t === 'string') out.add(t)
  else if (t && typeof t === 'object') for (const [key, v] of Object.entries(t)) { out.add(key); namesIn(v, out) }
  return out
}
const fresh = (used: Set<string>, prefix: string): string => {
  let i = 0
  while (used.has(`${prefix}${i}`)) i++
  const name = `${prefix}${i}`; used.add(name); return name
}
const limit = (n: number | undefined, fallback: number, cap: number): number =>
  n === undefined ? fallback : Number.isSafeInteger(n) && n >= 0 ? Math.min(n, cap) : 0

type Formula = boolean | {atom: string} | {op: 'not', a: Formula} | {op: 'and' | 'or', xs: Formula[]}
function condition(c: C, atoms: Map<string, C>): Formula | undefined {
  if (c.op === 'flag' || c.op === 'all') return undefined
  if (c.op === 'not') { const a = condition(c.x, atoms); return a === undefined ? undefined : {op: 'not', a} }
  if (c.op === 'and' || c.op === 'or') {
    const xs = c.xs.map(v => condition(v, atoms))
    return xs.some(v => v === undefined) ? undefined : {op: c.op, xs: xs as Formula[]}
  }
  const key = stable(c); atoms.set(key, c); return {atom: key}
}
function booleanBody(e: E, atoms: Map<string, C>): Formula | undefined {
  if (e.op === 'const') return e.value === 0 ? false : e.value === 1 ? true : undefined
  if (e.op !== 'if') return undefined
  const c = condition(e.c, atoms), a = booleanBody(e.then, atoms), b = booleanBody(e.else, atoms)
  if (c === undefined || a === undefined || b === undefined) return undefined
  return {op: 'or', xs: [{op: 'and', xs: [c, a]}, {op: 'and', xs: [{op: 'not', a: c}, b]}]}
}
const evaluate = (f: Formula, values: Map<string, boolean>): boolean => typeof f === 'boolean' ? f
  : 'atom' in f ? values.get(f.atom)!
  : f.op === 'not' ? !evaluate(f.a, values)
  : f.op === 'and' ? f.xs.every(x => evaluate(x, values)) : f.xs.some(x => evaluate(x, values))
const abs = (n: bigint) => n < 0n ? -n : n
const gcd = (a: bigint, b: bigint): bigint => { while (b) { const r = a % b; a = b; b = r } return abs(a) }
const primitive = (a: bigint[], b: bigint[]) => {
  const d = [...a, ...b].reduce(gcd, 0n)
  if (d > 1n) { for (let i = 0; i < a.length; i++) a[i] = a[i]! / d; for (let i = 0; i < b.length; i++) b[i] = b[i]! / d }
}

/** Propose Boolean identities, subset bounds and quorum intersection instances.
 * At most 2^maxAtoms rows per same-bound group. Non-Boolean counts and over-wide
 * groups are reported, never silently treated as sets. Atom valuations deliberately
 * overapproximate arithmetic: the kernel, not this table, decides their feasibility.
 */
export function proposeCountFacts(counts: Count[], context: unknown = [], options: CountFactOptions = {}): CountFacts {
  const out: CountFacts = {insts: [], regions: [], skipped: []}
  const used = namesIn([counts, context]); for (const s of options.reserved ?? []) used.add(s)
  const key = fresh(used, 'region$key$'), atomCap = limit(options.maxAtoms, 8, 12)
  const countCap = limit(options.maxCounts, 64, 128), factCap = limit(options.maxFacts, 256, 4096)
  const groups = new Map<string, Count[]>(), seen = new Set<string>()
  for (const c of counts) {
    if (seen.has(c.v)) { out.skipped.push({count: c.v, reason: 'duplicate count name'}); continue }
    seen.add(c.v)
    const bound = stable(c.below), group = groups.get(bound) ?? []
    group.push(c); groups.set(bound, group)
  }
  const emitted = new Set<string>()
  const emit = (cs: Count[], coeff: bigint[], below: E) => {
    if (out.insts.length >= factCap || coeff.some(c => abs(c) > BigInt(Number.MAX_SAFE_INTEGER))) return
    const terms: [number, string][] = cs.flatMap((c, i) => coeff[i] ? [[Number(coeff[i]), c.v] as [number, string]] : [])
    const unit = Number(coeff[cs.length] ?? 0n)
    if (!terms.length && unit === 0) return
    const signature = stable([below, terms, unit]); if (emitted.has(signature)) return
    emitted.add(signature)
    out.insts.push({wit: fresh(used, 'region$w$'), below, terms, unit})
  }
  for (const group of groups.values()) {
    const atoms = new Map<string, C>(), cs: Count[] = [], fs: Formula[] = []
    for (const c of group) {
      if (cs.length >= countCap) { out.skipped.push({count: c.v, reason: 'count cap'}); continue }
      const local = new Map<string, C>(), f = booleanBody(substE(c.body, {vars: {[c.key]: x(key)}, maps: {}, flags: {}}), local)
      if (f === undefined) { out.skipped.push({count: c.v, reason: 'non-Boolean body'}); continue }
      if (new Set([...atoms.keys(), ...local.keys()]).size > atomCap) { out.skipped.push({count: c.v, reason: 'atom cap'}); continue }
      for (const [a, c] of local) atoms.set(a, c)
      cs.push(c); fs.push(f)
    }
    if (!cs.length) continue
    const below = cs[0]!.below, keys = [...atoms.keys()]
    const rows = Array.from({length: 2 ** keys.length}, (_, bits) => {
      const values = new Map(keys.map((k, i) => [k, !!(bits & (1 << i))]))
      return fs.map(f => Number(evaluate(f, values)))
    })
    out.regions.push({below, atoms: [...atoms.values()], counts: cs.map(c => c.v), rows})
    // Integer column elimination gives every independent identity among declared
    // counts and the universe. Track exact coefficients; no floating-point rank.
    const basis: {pivot: number, col: bigint[], coeff: bigint[]}[] = []
    for (let j = 0; j <= cs.length; j++) {
      const col = rows.map(row => BigInt(j === cs.length ? 1 : row[j]!))
      const coeff: bigint[] = Array.from({length: cs.length + 1}, (_, i) => i === j ? 1n : 0n)
      for (const b of basis) {
        const a = col[b.pivot]!, d = b.col[b.pivot]!
        if (!a) continue
        for (let i = 0; i < col.length; i++) col[i] = d * col[i]! - a * b.col[i]!
        for (let i = 0; i < coeff.length; i++) coeff[i] = d * coeff[i]! - a * b.coeff[i]!
        primitive(col, coeff)
      }
      const pivot = col.findIndex(x => x !== 0n)
      if (pivot < 0) { emit(cs, coeff, below); emit(cs, coeff.map(c => -c), below) }
      else basis.push({pivot, col, coeff})
    }
    for (let a = 0; a < cs.length; a++) {
      const coeff = new Array<bigint>(cs.length + 1).fill(0n)
      coeff[a] = 1n; coeff[cs.length] = -1n; emit(cs, coeff, below)
      for (let b = 0; b < cs.length; b++) if (a !== b) {
        if (rows.every(row => row[a]! <= row[b]!)) {
          const sub = new Array<bigint>(cs.length + 1).fill(0n); sub[a] = 1n; sub[b] = -1n; emit(cs, sub, below)
        }
        // The alternative is a common-member witness, not an unconditional bound.
        if (a < b) { const meet = new Array<bigint>(cs.length + 1).fill(0n); meet[a] = 1n; meet[b] = 1n; meet[cs.length] = -1n; emit(cs, meet, below) }
      }
    }
  }
  return out
}

export type CountPickAudit = {count: string, below: number, abstract: number, actual?: number, reason?: string}

/** Ask for the existing distinct-key lower-bound rule at concrete member keys.
 * The evaluator is supplied by the caller's model. It is only a heuristic: even
 * a lying evaluator cannot bypass checkMC's pickHyp, which re-reads each body.
 * Both scanning and certificate size are bounded; large universes are reported.
 */
export function proposeCountPicks(counts: Count[], valueOf: (e: E) => number,
  options: {maxBelow?: number, maxKeys?: number} = {}): {picks: [string, E[]][], audit: CountPickAudit[]} {
  const picks: [string, E[]][] = [], audit: CountPickAudit[] = []
  const maxBelow = limit(options.maxBelow, 256, 4096), maxKeys = limit(options.maxKeys, 32, 256)
  for (const c of counts) {
    const below = valueOf(c.below), abstract = valueOf(x(c.v))
    const row: CountPickAudit = {count: c.v, below, abstract}; audit.push(row)
    if (!Number.isSafeInteger(below) || below < 0 || below > maxBelow || !Number.isSafeInteger(abstract) || abstract < 0) {
      row.reason = 'bound/value outside scan budget'; continue
    }
    let actual = 0, selected = 0
    const keys: E[] = []
    for (let k = 0; k < below; k++) {
      const term: E = {op: 'const', value: k}
      const value = valueOf(substE(c.body, {vars: {[c.key]: term}, maps: {}, flags: {}}))
      if (!Number.isSafeInteger(value) || value < 0 || !Number.isSafeInteger(actual + value)) { row.reason = 'non-natural/unsafe body sum'; break }
      actual += value
      if (value > 0 && keys.length < maxKeys && selected <= abstract) { keys.push(term); selected += value }
    }
    if (row.reason) continue
    row.actual = actual
    if (selected > abstract) picks.push([c.v, keys])
    else if (actual > abstract) row.reason = 'pick key cap'
  }
  return {picks, audit}
}

/** Instantiate existing machine reads, including packed two-parameter keys.
 * Mirrors the untrusted side of toCount; mcGoal/checkMC remain the authority.
 * Returns undefined rather than guessing a decomposition the checker won't use.
 */
export function countsForReads(decls: CountDecl[], reads: MapRead[]): Count[] | undefined {
  const out: Count[] = []
  for (const [v, map, term] of reads) {
    const d = decls.find(d => d.map === map); if (!d) return undefined
    const base = d.base ?? 0, lo = d.lo ?? d.j
    if (base && !(term.op === 'add' && term.a.op === 'mul' && term.a.k === base)) return undefined
    const hi: E = base && term.op === 'add' && term.a.op === 'mul' ? term.a.a : {op: 'const', value: 0}
    const low = base && term.op === 'add' ? term.b : term
    const at = {vars: {[d.j]: hi, [lo]: low}, maps: {}, flags: {}}
    out.push({v, key: d.key, below: substE(d.below, at), body: substE(d.body, at)})
  }
  return out
}
