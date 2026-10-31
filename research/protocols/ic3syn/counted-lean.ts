// The counting class's proofs, found with nothing written (core/counts.ts), exported to Lean through CountMachine.lean's
// cmachine_sound (lean-kernel/emit.ts's cmachineToLean): `bun counted-lean.ts <dir> id,id` writes CountedIC3.lean.
import {writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {searchCounted} from '../../../core/counts.ts'
import {cmachineToLean} from '../../../lean-kernel/emit.ts'
import {protocols} from './models.ts'

const [dir = '.', only = 'toy_consensus,quorum_leader_election,toy_consensus_forall'] = process.argv.slice(2)
const parts: string[] = [], ids: string[] = []
for (const [j, id] of only.split(',').entries()) {
  const p = protocols.find(q => q.id === id)!, r = p.make()
  const c = searchCounted(r.machine, [...(r as any).kindLaws(), ...p.laws(r)], 120_000)
  if (!c.proven || !c.proof) throw new Error(`${id}: not proven (${c.why})`)
  parts.push(cmachineToLean(`ic${j}`, c.m, c.laws, c.proof)); ids.push(`ic${j}_laws`)
  console.log(`${id}: ${c.laws.length} laws exported`)
}
writeFileSync(join(dir, 'CountedIC3.lean'), `import CountMachine
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

${parts.join('\n\n')}

${ids.map(i => `#print axioms ${i}`).join('\n')}
`)
