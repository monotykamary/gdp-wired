// The ∀∃ class's proofs, found with nothing written (core/exists.ts's ghost maps, core/infer.ts's search for the laws
// beside them), exported to Lean through GhostMap.lean (lean-kernel/emit.ts's smachineToLean with `ghosted`): the
// ghosted machine's laws by smachine_sound, the original's by smghost_laws, and the law with "there exists" by
// forall_some_of_ghostmap. With `subst` (`bun ghosted-lean.ts <dir> id,id subst`), the route core/dsl.ts's verdict takes:
// exists.ts's skolemOf ghosts, the plain laws and the search's found laws proven of the ghosted machine, each law with
// "there exists" admitted by kernel.ts's someOfGhostsOk and read by forall_some_of_ghostsubst. Writes GhostedIC3.lean.
import {writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {proveSome, skolemOf} from '../../../core/exists.ts'
import {inferLaws} from '../../../core/infer.ts'
import {proveRule} from '../../../core/dsl.ts'
import {type Law} from '../../../core/machine.ts'
import {type Ghosted, checkGhostedLaws, ghostedMachine, someOfGhostsOk} from '../../../kernel/kernel.ts'
import {proveLaws} from '../../../kernel/prove.ts'
import {smachineToLean} from '../../../lean-kernel/emit.ts'
import {protocols} from './models.ts'

const [dir = '.', only = 'client_server_ae', route] = process.argv.slice(2)
const parts: string[] = [], ids: string[] = []
for (const [j, id] of only.split(',').entries()) {
  const p = protocols.find(q => q.id === id)!, r: any = p.make(), m = r.machine, laws: Law[] = [...r.kindLaws(), ...p.laws(r)]
  if (route === 'subst') {
    const stated: Law[] = p.laws(r), sk = skolemOf(m, stated)
    if (!sk) throw new Error(`${id}: no plain form`)
    const G: Ghosted = {orig: m, vars: {}, maps: sk.maps}, gm = ghostedMachine(G), found = (proveRule(r, stated, {search: {ms: 60_000}}).found?.laws ?? []) as {law: Law}[]
    const ls = [...r.kindLaws() as Law[], ...sk.laws, ...found.map(f => f.law)], out = proveLaws(gm, ls)
    if (!out.proven || !out.proof || !checkGhostedLaws(G, ls, out.proof as never)) throw new Error(`${id}: the plain laws not proven of the ghosted machine`)
    const exs = stated.filter(l => l.some?.length)
    if (!exs.every(l => someOfGhostsOk(G, l, sk.plains[l.name]!.plain, sk.plains[l.name]!.sub))) throw new Error(`${id}: someOfGhostsOk refuses`)
    parts.push(smachineToLean(`gh${j}`, gm, ls, {ghosted: G, ghostSubst: exs.map(l => ({law: sk.plains[l.name]!.plain.name, body: l.holds, sub: sk.plains[l.name]!.sub})),
      free: exs.flatMap(l => l.some!), noFacts: !(gm.facts ?? []).length}))
    ids.push(`gh${j}_orig_laws`, `gh${j}_skolem`, ...exs.map((_, i) => `gh${j}_ex${i}`))
    console.log(`${id}: ${ls.length} laws, ghosts ${Object.keys(sk.maps).join(', ')}`)
    continue
  }
  // (the laws the search adds, where the ∃ law with its ghost map alone isn't inductive)
  let out = proveSome(m, laws)
  // (or proveRule's search: a law with "there exists" about keys searched in its plain form over its ghost map)
  if (!out.proven) out = proveSome(m, [...laws, ...((proveRule(r, p.laws(r), {search: {ms: 60_000}}).found?.laws ?? []) as {law: Law}[]).map(f => f.law)])
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
