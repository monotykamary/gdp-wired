// Generic proof-output bridge: export only the retained weighted family,
// then prove source correspondence (flag views, observer, ghost map, sum).
import assert from 'node:assert/strict'
import type {Law,Machine} from '../../core/machine.ts'
import {type Instances,type Tree,checkLaws,ghostedOk,sideGoals} from '../../kernel/kernel.ts'
import {retainedSumMachineToLean} from '../../lean-kernel/emit.ts'
import type {WeightedCandidate} from './weighted.ts'

export function emitWeighted(c: WeightedCandidate, source: Machine, law: Law,
    proof: {instances: Record<string, Instances>, trees: Record<string, Tree>}): string {
  assert(law.forall&&!law.keys?.length&&!law.some?.length)
  assert(ghostedOk(c.ghost))
  assert.equal(sideGoals(c.machine,c.laws).length,0,'unexpected cover search')
  assert(checkLaws(c.machine,c.laws,proof),'exact native weighted family rejected')
  const [g,...extra]=Object.keys(c.ghost.maps)
  assert(g&&extra.length===0&&Object.keys(c.ghost.vars).length===0)
  const idx=c.laws.findIndex(l=>l.name===law.name)
  assert(idx>=0)
  const body=retainedSumMachineToLean('packet',c.machine,c.laws,proof,{free:[law.forall],after:(ix,mx,lit,cond)=>{
    const flags=Object.entries(c.ghost.orig.step.flags??{})
    const binder=flags.map(([f,a])=>{assert.equal(a.op,'all');assert(a.op==='all'&&!a.keys?.length);return `if i = ${ix(`?${f}`)} then ${ix(a.key)} else `}).join('')+'0'
    const goal=cond(law.holds), specialization=cond(c.laws[idx]!.holds)
    return `
def originalMachine : SMachine := ${lit(source)}
def unchangedLaw : MLaw := ⟨${goal}, some ${ix(law.forall!)}⟩
def observer : Nat := ${ix(c.observer)}
def closedBinder (i : Nat) : Nat := ${binder}
def mapLift : SGhostedM := ⟨${lit(c.ghost.orig)}, [], [(${mx(g)}, ${c.ghost.maps[g]!.start})],
  packet_sums.s.f.m.writes.filter (fun row => row.1 == ${mx(g)}), []⟩
theorem liftChecks : smghostOk mapLift = true := by decide +kernel
theorem sumShape : mapLift.full = packet_sums.s := by rfl
theorem sumGhostChecks : sghostOk packet_sums.ghosts = true := by decide +kernel
theorem promotionIdentity : mapLift.orig = GroupedSumsResearch.promote originalMachine closedBinder mapLift.orig.wits := by rfl

theorem unchanged_law (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (hr : SReach originalMachine ρ M) : unchangedLaw.Holds ρ M := by
  intro k
  have ho := GroupedSumsResearch.source_rebind originalMachine observer rfl rfl rfl (by decide +kernel) hr k
  have hc : SReach mapLift.orig (upd ρ observer k) M :=
    (GroupedSumsResearch.candidate_reach closedBinder _ promotionIdentity rfl (by decide +kernel)).mpr ho
  obtain ⟨ρg, Mg, hg, hs, hm⟩ := smghost_reach mapLift liftChecks hc
  have he : packet_e${idx}.Holds ρg Mg :=
    sum_project_laws packet_sums sumGhostChecks packet_proof packet_check packet_scheck
      ρg Mg (sumShape ▸ hg) packet_e${idx} (by simp [packet_proof]) (by decide +kernel)
  have hl : packet_e${idx}.Holds (upd ρ observer k) M :=
    sentry_transfer (V := mapLift.vars) (MS := mapLift.maps) (by decide +kernel) (by decide +kernel)
      (fun i hi => (hs i hi).symm) (fun m hmi => (hm m hmi).symm) he
  change evalC (upd ρ observer k) M (${specialization}) = true at hl
  change evalC (upd ρ ${ix(law.forall!)} k) M (${goal}) = true
  simpa [observer, evalC, evalE, upd] using hl

theorem aggregate_claim : ∀ ρ M, SReach originalMachine ρ M → unchangedLaw.Holds ρ M :=
  unchanged_law
`
  }})
  return `import GhostMap\nimport Sums\nimport GroupedTransport\nopen Kern Cert\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n${body}`
}
