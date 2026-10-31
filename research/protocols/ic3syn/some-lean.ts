// The top-level ∃ class's proofs, found with nothing written (core/dsl.ts's someCone: core/exists.ts's ghostOf for the
// witness, the engine's cubes kept for support), exported to Lean through the suite's path (lean-kernel/emit.ts's toLean:
// the ∃ law with its ghost, Ghost.lean's). `bun some-lean.ts <id> <ms> <out.lean>` prints one JSON line.
import {writeFileSync} from 'node:fs'
import {proveRule} from '../../../core/dsl.ts'
import {ghostOf} from '../../../core/exists.ts'
import {type Law} from '../../../core/machine.ts'
import {toLean} from '../../../lean-kernel/emit.ts'
import {protocols} from './models.ts'

const [id = 'simple', ms0, file = '/tmp/p.lean'] = process.argv.slice(2)
const p = protocols.find(q => q.id === id)!, r: any = p.make(), laws: Law[] = p.laws(r)
const v: any = proveRule(r, laws, {search: {ms: Number(ms0 ?? 60_000)}}), out: Record<string, unknown> = {id, verdict: v.proven && v.checked ? 'proven' : 'unknown'}
if (v.proven && v.checked) {
  // (the ∃ law with the witness the search chose, beside the laws it kept)
  const found: Law[] = (v.found?.laws ?? []).map((f: any) => f.law), witnessed = laws.map(l => (l.some?.length && !l.forall ? {...l, witness: ghostOf(r.machine, l)} : l))
  const set = [...r.kindLaws().filter((k: Law) => ![...witnessed, ...found].some(l => l.name === k.name)), ...witnessed, ...found.filter(f => !witnessed.some(l => l.name === f.name))]
  const text = toLean([{id, machine: r.machine, laws: set}], {title: id})
  writeFileSync(file, text)
  Object.assign(out, {laws: set.length, bytes: text.length})
}
console.log(JSON.stringify(out))
process.exit(0)
