// A diagnosis, not a search: a counted protocol's search (core/counts.ts) with laws written by hand added to its callers,
// so whether a goal that ends with a model lacks a supporting law (the hints prove it) or an instance (they don't).
//   GDP_COUNTS_TRACE=1 bun research/protocols/engine/hintprobe.ts <id> <hint,hint|none> [ms]
import {forall} from '../../../core/dsl.ts'
import {searchCounted} from '../../../core/counts.ts'
import {N, pk} from '../ic3syn/common.ts'
import {protocols} from '../ic3syn/models.ts'

const [id = 'consensus_forall', which = 'none', ms = '300000'] = process.argv.slice(2)
const p = protocols.find(q => q.id === id)!, r: any = p.make()
// (values below N, not below size: the decided value's place)
const hints: Record<string, () => unknown> = {
  lead: () => r.law('H a decision is a leader\'s', ({size, Decided, Leader}: any) => forall((a, x) => a.lt(size).and(x.lt(N), Decided.at(pk(a, x))).implies(Leader.at(a)))),
  once: () => r.law('H one decision a node', ({size, Decided}: any) => forall((a, x, y) => a.lt(size).and(x.lt(N), y.lt(N), Decided.at(pk(a, x)), Decided.at(pk(a, y))).implies(x.eq(y)))),
}
const extra = which === 'none' ? [] : which.split(',').map(h => hints[h]!())
const t0 = performance.now(), c = searchCounted(r.machine, [...r.kindLaws(), ...p.laws(r), ...extra] as any, Number(ms))
console.log(JSON.stringify({id, hints: which, proven: c.proven, why: c.why, laws: c.laws.length, ms: Math.round(performance.now() - t0)}))
