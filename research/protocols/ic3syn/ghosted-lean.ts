// The ∀∃ class's proofs, found with nothing written (core/exists.ts's ghost maps, core/infer.ts's search for the laws
// beside them), exported to Lean through GhostMap.lean (lean-kernel/emit.ts's smachineToLean with `ghosted`): the
// ghosted machine's laws by smachine_sound, the original's by smghost_laws, and the law with "there exists" by
// forall_some_of_ghostmap. `bun ghosted-lean.ts <dir> id,id` writes GhostedIC3.lean.
import {writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {proveSome} from '../../../core/exists.ts'
import {inferLaws} from '../../../core/infer.ts'
import {type Law} from '../../../core/machine.ts'
import {type Ghosted, checkGhostedLaws} from '../../../kernel/kernel.ts'
import {smachineToLean} from '../../../lean-kernel/emit.ts'
import {protocols} from './models.ts'

const [dir = '.', only = 'client_server_ae'] = process.argv.slice(2)
const parts: string[] = [], ids: string[] = []
for (const [j, id] of only.split(',').entries()) {
  const p = protocols.find(q => q.id === id)!, r: any = p.make(), m = r.machine, laws: Law[] = [...r.kindLaws(), ...p.laws(r)]
  // (the laws the search adds, where the ∃ law with its ghost map alone isn't inductive)
  let out = proveSome(m, laws)
  if (!out.proven) out = proveSome(m, [...laws, ...inferLaws(r, laws, [], {ms: 120_000}).found.map(f => f.law)])
  const exLaw = out.laws?.find(l => l.ex?.map)
  if (!out.proven || !out.machine || !out.laws || !out.proof || !exLaw) throw new Error(`${id}: not proven with a ghost map (${out.failed?.why ?? out.failed?.stuck})`)
  const W = exLaw.ex!.map!.name, gm = out.machine, {[W]: _w, ...maps} = gm.maps ?? {}, {[W]: write, ...writes} = gm.step.maps ?? {}
  const g: Ghosted = {orig: {...gm, maps, step: {...gm.step, maps: writes}}, vars: {}, maps: {[W]: {start: 0, write: write as never}}}
  if (!checkGhostedLaws(g, out.laws, out.proof as never)) throw new Error(`${id}: kernel.ts refuses the ghosted laws`)
  // (a law about one key read ∀∃ by forall_some_of_ghostmap; about several, by some_of_ghostmap alone: at every reachable
  // state of the original, ghost maps where every law holds, the law with its witness at W among them)
  const one = !exLaw.keys?.length, forallSome = one ? [{law: exLaw.name, map: W, at: exLaw.ex!.map!.at, as: 'x'}] : []
  parts.push(smachineToLean(`gh${j}`, gm, out.laws.map(({ex: _ex, ...l}) => l), {ghosted: g, forallSome, free: one ? ['x'] : [], noFacts: !(gm.facts ?? []).length}))
  ids.push(`gh${j}_orig_laws`, `gh${j}_skolem`, ...(one ? [`gh${j}_some0`] : []))
  console.log(`${id}: ${out.laws.length} laws, ${W} at ${JSON.stringify(exLaw.ex!.map!.at)}`)
}
writeFileSync(join(dir, 'GhostedIC3.lean'), `import GhostMap
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

${parts.join('\n\n')}

${ids.map(i => `#print axioms ${i}`).join('\n')}
`)
