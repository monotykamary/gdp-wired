import PaxosEprConcreteWalk
import PaxosEprAtomicGuards
import PaxosEprAtomicBoolean
namespace Bapa.PaxosEprSourceScan
open Kern Bapa.FiniteSimulation

def atomicStore (ρ : Nat → Nat) (M : Nat → Nat → Nat) : PaxosEprTarget.ScanStore := ⟨ρ 0,ρ 3,M⟩

/-- Concrete scan completion from the unchanged source's admitted request and
actual quantified flags. The missing start edge is explicit in `ready`, not
assumed to be reachable or hidden in an unproved encoding theorem. -/
theorem source_ready_scan_finishes {ρ : Nat → Nat} {M : Nat → Nat → Nat}
    (sourceReach : CReach PaxosEprAtomicSource.machine PaxosEprAtomicSource.declarations ρ M) (ι : Nat → Nat) (κ : Nat → Nat → Nat)
    (admitted : evalC (sView PaxosEprAtomicSource.machine ρ M ι κ).1 (sView PaxosEprAtomicSource.machine ρ M ι κ).2 PaxosEprAtomicSource.machine.f.m.assume = true)
    (rowsFlag : (sView PaxosEprAtomicSource.machine ρ M ι κ).1 13 = 1)
    (quorumFlag : (sView PaxosEprAtomicSource.machine ρ M ι κ).1 19 = 1)
    {x : KState} (ready : PaxosEprTarget.During (atomicStore ρ M) (κ 6) (ι 6) (ι 8) (ι 7) 0 x) :
    ∃ y, CSteps PaxosEprTarget.machine PaxosEprTarget.declarations x y ∧ PaxosEprTarget.Finished (atomicStore ρ M) (ι 6) (ι 7) y := by
  have hs : PaxosEprTarget.StoreBoolean (atomicStore ρ M) := by
    intro mp hm key
    exact PaxosEprAtomicSource.counted_reachable_boolean sourceReach mp hm key
  have hq : ∀ key, κ 6 key ≤ 1 := fun key => (PaxosEprAtomicSource.quorumValid_from_flag ρ M ι κ quorumFlag key).1
  have hr : PaxosEprTarget.AllRows (atomicStore ρ M) (κ 6) (ι 6) (ι 8) := by
    intro i _ hi rr vv hv hlt
    have hpositive : 1 ≤ κ 6 i := by rw [hi]; omega
    exact PaxosEprAtomicSource.reachable_voteRows_unbounded sourceReach ι κ rowsFlag i rr vv hpositive hv hlt
  have hp : 0 < (atomicStore ρ M).size := PaxosEprAtomicSource.admitted_size_positive ρ M ι κ admitted
  exact PaxosEprTarget.finish_concrete_scan (atomicStore ρ M) (κ 6) (ι 6) (ι 8) (ι 7) hs hq hr hp ready

#print axioms source_ready_scan_finishes
end Bapa.PaxosEprSourceScan
