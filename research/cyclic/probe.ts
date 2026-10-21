// Each cyclic goal of a machine's laws, grown on its own and timed: `bun research/cyclic/probe.ts <trees|sheet>`.
import {searchTree, searchTreeLaws, sheet, sheetLaws} from '../../examples/trees.ts'
import {machineNodes} from '../../core/cyclic.ts'
import {mainGoal} from '../../kernel/cyclic.ts'
import {grow, proveLaws} from '../../kernel/prove.ts'
import type {Law, Machine} from '../../core/machine.ts'

const which = process.argv[2] ?? 'trees'
const [m, laws]: [Machine, Law[]] = which === 'sheet' ? [sheet().machine, [...sheet().kindLaws(), ...sheetLaws()]] : [searchTree().machine, [...searchTree().kindLaws(), ...searchTreeLaws()]]
const out = proveLaws(m, laws)
const {facts, specs} = machineNodes(m, laws, out.proof!.instances)
for (const sp of specs) {
  const g = mainGoal(facts, specs, sp), t = performance.now(), r = grow(g)
  console.log(`${sp.name}: ${'tree' in r ? 'proven' : r.stuck} ${Math.round(performance.now() - t)} ms, ${'tree' in r ? r.nodes : ''} nodes`)
}
