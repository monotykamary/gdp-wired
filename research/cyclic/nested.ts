// The laws that read a map at a key read from a map (core/cyclic.ts's uncoveredWhy: the search tree's and the sheet's),
// their usual proofs translated as any machine's are (machineNodes with the usual trees), each node's goal timed:
// `bun research/cyclic/nested.ts <trees|sheet> [ms]`. Prints the translation's verdict, its time against the usual
// proof's, and the slowest goals.
import {searchTree, searchTreeLaws, sheet, sheetLaws} from '../../examples/trees.ts'
import {machineNodes, proveCyclic} from '../../core/cyclic.ts'
import {tstats} from '../../core/translate.ts'
import {proveLaws, withDeadline} from '../../kernel/prove.ts'
import type {Law, Machine} from '../../core/machine.ts'

const which = process.argv[2] ?? 'trees', ms = Number(process.argv[3] ?? 120_000)
const [m, laws]: [Machine, Law[]] = which === 'sheet' ? [sheet().machine, [...sheet().kindLaws(), ...sheetLaws()]] : [searchTree().machine, [...searchTree().kindLaws(), ...searchTreeLaws()]]
let t = performance.now()
const out = proveLaws(m, laws), usualMs = performance.now() - t
console.log(`${m.name}: usual ${out.proven && out.checked ? 'proven' : 'not proven'} in ${Math.round(usualMs)} ms`)
t = performance.now()
const st = tstats(), b = machineNodes(m, laws, out.proof!.instances, out.proof!, st)
console.log(`nodes: ${b.specs.length}${b.why ? `, why: ${b.why}` : ''} (${Math.round(performance.now() - t)} ms)`)
if (!b.why) {
  t = performance.now()
  const v = withDeadline(performance.now() + ms, () => proveCyclic(b.facts, b.specs, undefined, undefined, st))
  console.log(`cyclic: ${v.proven ? `proven, checked ${v.checked}` : `not proven: ${v.node}: ${v.goal}: ${String(v.stuck).slice(0, 300)}`} in ${Math.round(performance.now() - t)} ms; ${JSON.stringify(st)}`)
}
