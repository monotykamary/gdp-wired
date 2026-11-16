import PaxosEprSourceProposeGuards
import PaxosEprTargetStartExecution
import PaxosEprSourceScan
namespace Bapa.PaxosEprSourceScan
open Kern Bapa.FiniteSimulation

structure Idle (s : PaxosEprTarget.ScanStore) (x : KState) : Prop where
 none : x.1 0 = s.none
 size : x.1 1 = s.size
 busy : x.1 8 = 0
 count : x.1 9 = 0
 round : x.1 10 = 0
 maxRound : x.1 11 = 0
 value : x.1 12 = 0
 publicMaps : ∀ mp, mp < 6 → ∀ key, x.2 mp key = s.maps mp key
 quorum : ∀ key, x.2 6 key = 0

/-- An admitted, enabled atomic-source Propose drives an actual counted target
walk from idle through START and all nodes. No ready-state or semantic guard
is assumed: those are extracted from the source request and its reachability. -/
theorem source_propose_scans {ρ : Nat → Nat} {M : Nat → Nat → Nat}
 (reach : CReach PaxosEprAtomicSource.machine PaxosEprAtomicSource.declarations ρ M)
 (ι : Nat → Nat) (κ : Nat → Nat → Nat)
 (hg : GHolds PaxosEprAtomicSource.declarations
   (withInputs PaxosEprAtomicSource.machine.f.m.inputs ρ ι) (withCarried PaxosEprAtomicSource.machine M κ))
 (ha : evalC (sView PaxosEprAtomicSource.machine ρ M ι κ).1 (sView PaxosEprAtomicSource.machine ρ M ι κ).2 PaxosEprAtomicSource.machine.f.m.assume = true)
 (hp : (sView PaxosEprAtomicSource.machine ρ M ι κ).1 16 = 1)
 {x : KState} (hx : Idle (atomicStore ρ M) x) :
 ∃ y, CSteps PaxosEprTarget.machine PaxosEprTarget.declarations x y ∧
   PaxosEprTarget.Finished (atomicStore ρ M) (ι 6) (ι 7) y := by
 obtain ⟨hop,hr,hnp,hj,hrw,hm⟩ := PaxosEprAtomicSource.Propose.actual_guard ρ M ι κ hp
 obtain ⟨hn,hw,hq,hmajor⟩ := PaxosEprAtomicSource.Propose.actual_admission ρ M ι κ hop ha
 have q := PaxosEprAtomicSource.quorumValid_from_flag ρ M ι κ hq
 have bool := PaxosEprAtomicSource.counted_reachable_boolean reach
 have xb : PaxosEprTarget.BooleanSeven x.2 := by
  intro mp hmp key
  by_cases he : mp = 6
  · subst mp
    rw [hx.quorum]
    omega
  · rw [hx.publicMaps mp (by omega)]
    exact bool mp (by omega) key
 have qx : ∀ k, κ 6 k ≤ 1 ∧ (1 ≤ κ 6 k → k < x.1 1) := by
  intro k
  simpa only [hx.size,atomicStore] using q k
 have maj : x.1 1 < 2 * PaxosEprTarget.quorumCount (x.1 1) (κ 6) := by
  have hc := PaxosEprTarget.source_members_count ρ M ι κ hg
  simpa only [hx.size,atomicStore,hc] using hmajor
 have nx : ∀ z, x.2 3 (cpair (ι 6) z) ≠ 1 := by
  intro z
  rw [hx.publicMaps 3 (by decide)]
  have hz := PaxosEprAtomicSource.reachable_noProposal_unbounded reach ι κ hnp z
  change M 3 (cpair (ι 6) z) ≠ 1
  rw [hz]
  decide
 have jx : ∀ k, 1 ≤ κ 6 k → x.2 1 (cpair (ι 6) k) = 1 := by
  intro k hk
  rw [hx.publicMaps 1 (by decide)]
  have lo := PaxosEprAtomicSource.joined_from_flag ρ M ι κ hj k hk
  have hi := bool 1 (by decide) (cpair (ι 6) k)
  change M 1 (cpair (ι 6) k) = 1
  omega
 have mx : ι 8 = x.1 0 ∨ (1 ≤ κ 6 (ι 9) ∧ ι 8 < ι 6 ∧ x.2 4 (cpair (ι 9) (cpair (ι 8) (ι 7))) = 1) := by
  rcases hm with hnone | ⟨hmember,hlt,hvote⟩
  · exact .inl (hnone.trans hx.none.symm)
  · refine .inr ⟨hmember,hlt,?_⟩
    rw [hx.publicMaps 4 (by decide)]
    have hi := bool 4 (by decide) (cpair (ι 9) (cpair (ι 8) (ι 7)))
    change M 4 (cpair (ι 9) (cpair (ι 8) (ι 7))) = 1
    omega
 have rows : PaxosEprTarget.AllRows ⟨x.1 1,x.1 0,x.2⟩ (κ 6) (ι 6) (ι 8) := by
  intro k _ hmember r v hv hl
  have hv' : M 4 (cpair k (cpair r v)) = 1 := by simpa only [hx.publicMaps 4 (by decide),atomicStore] using hv
  have hpos : 1 ≤ κ 6 k := by omega
  have h := PaxosEprAtomicSource.reachable_voteRows_unbounded reach ι κ hrw k r v hpos hv' hl
  simpa only [hx.none,atomicStore] using h
 obtain ⟨y,path,done⟩ := PaxosEprTarget.target_propose_walk x.1 x.2 (ι 5) (ι 6) (ι 7) (ι 8) (ι 9) (κ 6)
  hx.busy hx.count (by simpa only [hx.none,atomicStore] using hr) xb
  (by simpa only [hx.size,atomicStore] using hn) (by simpa only [hx.size,atomicStore] using hw)
  qx maj nx jx mx rows
 refine ⟨y,path,done.none.trans hx.none,done.size.trans hx.size,done.busy,done.count,done.round,done.maxRound,done.value,?_,done.quorum⟩
 intro mp hmp key
 have he := done.publicMaps mp hmp key
 dsimp only at he
 simpa only [hx.publicMaps mp hmp key] using he

#print axioms source_propose_scans
end Bapa.PaxosEprSourceScan
