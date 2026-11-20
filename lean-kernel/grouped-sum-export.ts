import type {Law, Machine} from '../core/machine.ts'
import {type GroupedSumCertificate, checkGroupedSum, groupedSumTheory} from '../kernel/grouped-sum.ts'
import {retainedSMachineToLean} from './emit.ts'

// Replay the retained proof trees verbatim via Kern.GroupedSums.grouped_sum_sound.
// No proof search runs at export time (`retainedSMachineToLean` pins `retainedOnly` and `decide +kernel`).
export function groupedSumToLean(id: string, source: Machine, law: Law, cert: GroupedSumCertificate): string {
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(id) || !checkGroupedSum(source, law, cert))
    throw new Error('invalid grouped-sum export')
  const {plain, observer, group, decls, initGoals, coverGoals, guardIndex} = groupedSumTheory(source, law, cert)!
  const free = [...new Set([
    ...(law.forall ? [law.forall] : []),
    ...decls.flatMap(d => [d.key, d.x, ...d.params]),
    ...[...initGoals, ...coverGoals].flatMap(g =>
      [...JSON.stringify(g.hyps).matchAll(/"op":"var","name":"([^"]+)"/g)].map(m => m[1]!)),
  ])]
  const body = retainedSMachineToLean('packet', plain, cert.laws, cert.proof, {
    free,
    after: (ix, _mx, lit, cond, expr, enc) => {
      const declLits = decls.map(d =>
        `⟨${ix(d.name)}, ${ix(d.key)}, [${d.params.map(p => String(ix(p))).join(', ')}], ${expr(d.term)}, [${d.covers.map(expr).join(', ')}], ${ix(`?${d.flag}`)}, ${ix(`w?${d.flag}`)}, ${ix(d.x)}⟩`)
      const initLits = initGoals.map(g => {
        const tree = cert.proof.trees[g.name]
        if (!tree) throw new Error(`${id}: missing retained init tree for ${g.name}`)
        const encoded = enc(g, tree)
        return `(${encoded.tab}, ${encoded.tree})`
      })
      const coverByName = new Map(coverGoals.map(g => [g.name, g]))
      const coverLits = decls.map(d => {
        const gs = Object.entries(source.step.maps ?? {}).flatMap(([mp, w]) => {
          if (!('each' in w) || !d.read.includes(mp)) return []
          const g = coverByName.get(`${d.name} @cover ${mp}`)
          if (!g) throw new Error(`${id}: missing cover goal for ${d.name} @cover ${mp}`)
          return [g]
        })
        return `[${gs.map(g => {
          const tree = cert.proof.trees[g.name]
          if (!tree) throw new Error(`${id}: missing retained cover tree for ${g.name}`)
          const encoded = enc(g, tree)
          return `(${encoded.tab}, ${encoded.tree})`
        }).join(', ')}]`
      })
      const keyOpt = law.forall ? `some ${ix(law.forall)}` : 'none'
      return `
def originalMachine : SMachine := ${lit(source)}
def unchangedLaw : MLaw := ⟨${cond(law.holds)}, ${keyOpt}⟩
def observer : Nat := ${ix(observer)}
def groupTerm : E := ${expr(group)}
def packet_psums : ParamSumMachine := ⟨originalMachine, [${declLits.join(', ')}]⟩
def packet_inits : List (List VDef × Tree) := [${initLits.join(', ')}]
def packet_covers : List (List (List VDef × Tree)) := [${coverLits.join(', ')}]

theorem packet_shape : packet_psums.plain = packet_machine := by rfl
theorem packet_pcheck : checkParamSums packet_psums packet_proof packet_inits packet_covers = true := by decide +kernel
theorem sumGhostChecks : sghostOk packet_psums.ghosts = true := by decide +kernel
theorem obsOk : observerOk originalMachine observer = true := by decide +kernel
theorem guardEq : packet_e${guardIndex}.law = guardLaw unchangedLaw observer groupTerm := by rfl
theorem guardAvoids : avoids packet_psums.ghosts.vars packet_e${guardIndex}.law.holds = true := by decide +kernel

theorem original_law (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (hr : SReach originalMachine ρ M) : unchangedLaw.Holds ρ M :=
  grouped_sum_sound packet_psums packet_proof packet_inits packet_covers
    observer groupTerm unchangedLaw packet_e${guardIndex}
    (packet_shape.symm ▸ packet_check) packet_pcheck sumGhostChecks obsOk
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by simp [packet_proof]) guardEq guardAvoids ρ M hr
`
    },
  })
  return `namespace ${id}
open Kern Cert Classical Kern.GroupedSums
set_option maxRecDepth 100000
set_option maxHeartbeats 0
${body}
end ${id}
#print axioms ${id}.packet_check
#print axioms ${id}.packet_pcheck
#print axioms ${id}.sumGhostChecks
#print axioms ${id}.obsOk
#print axioms ${id}.original_law
`
}
