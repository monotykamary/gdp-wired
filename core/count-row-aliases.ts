// Untrusted equality proposals for a row count and an identical existing read.
// Both inequalities remain ordinary CountInst witnesses checked by checkMC.
import {type CountCert, type CountDecl, substE} from '../kernel/kernel.ts'
import {type C, type E, x} from './machine.ts'
import {countsForReads} from './count-facts.ts'
export function identicalRowCountAliases(decls: CountDecl[], reads: CountCert['reads'], rowMap: string, prefix: string, more: () => boolean = () => true): CountCert['insts'] {
  const counts = countsForReads(decls, reads)
  if (!counts) return []
  const rows = new Set(reads.filter(([, map]) => map === rowMap).map(([id]) => id)), pre = new Set(reads.filter(([, map]) => !map.endsWith('#')).map(([id]) => id))
  const body = (c: typeof counts[number]) => JSON.stringify([c.below, substE(c.body, {vars: {[c.key]: x(prefix + 'bound')}, maps: {}, flags: {}})])
  const out: CountCert['insts'] = [], seen = new Set<string>()
  for (const row of counts.filter(c => rows.has(c.v))) for (const other of counts) {
    if (!more() || out.length >= 8) return out
    if (row.v === other.v || !pre.has(other.v) || body(row) !== body(other)) continue
    const pair = [row.v, other.v].sort().join('\n')
    if (seen.has(pair)) continue
    seen.add(pair)
    for (const [a, b] of [[row.v, other.v], [other.v, row.v]]) out.push({wit: prefix + out.length, below: row.below, terms: [[1, a!], [-1, b!]], unit: 0})
  }
  return out
}

// Equality is only a proposal here. A missing restriction is NOT assumed:
// each signed difference still needs an ordinary counting witness refutation.
// This includes the election's threshold/not-newer restricted count, rather
// than trying to repair only a plain membership-row alias. Keep the nearest
// predicate slice: do not drop both the threshold and a not-newer restriction.
export function restrictedRowCountAliases(decls: CountDecl[], reads: CountCert['reads'], voteMap: string, prefix: string, more: () => boolean = () => true): CountCert['insts'] {
  const counts = countsForReads(decls, reads)
  if (!counts) return []
  const votes = new Set(reads.filter(([, map]) => map === voteMap).map(([id]) => id)), pre = new Set(reads.filter(([, map]) => !map.endsWith('#')).map(([id]) => id))
  const atoms = (c: C): C[] => c.op === 'and' ? c.xs.flatMap(atoms) : [c]
  const body = (e: E): Set<string> | undefined => e.op === 'if' && e.then.op === 'const' && e.then.value === 1 && e.else.op === 'const' && e.else.value === 0 ? new Set(atoms(e.c).map(c => JSON.stringify(c))) : undefined
  const normalized = (c: typeof counts[number]) => body(substE(c.body, {vars: {[c.key]: x(prefix + 'bound')}, maps: {}, flags: {}}))
  const out: CountCert['insts'] = [], seen = new Set<string>()
  for (const vote of counts.filter(c => votes.has(c.v))) for (const other of counts) {
    if (!more() || out.length >= 8) return out
    if (vote.v === other.v || !pre.has(other.v) || JSON.stringify(vote.below) !== JSON.stringify(other.below)) continue
    const a = normalized(vote), b = normalized(other)
    if (!a || !b || !b.size || a.size > b.size + 1 || ![...b].every(atom => a.has(atom))) continue
    const pair = [vote.v, other.v].sort().join('\n')
    if (seen.has(pair)) continue
    seen.add(pair)
    for (const [left, right] of [[vote.v, other.v], [other.v, vote.v]]) out.push({wit: prefix + out.length, below: vote.below, terms: [[1, left!], [-1, right!]], unit: 0})
  }
  return out
}
