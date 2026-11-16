import PaxosEprFullSimulation
import PaxosEprTreeRepairChecks
namespace Bapa.PaxosEprSafetyGate
open Kern Bapa.PaxosEprSourceScan
set_option maxRecDepth 100000
set_option maxHeartbeats 0

deriving instance DecidableEq for E, C, MLaw, MMachine, FMMachine, SMachine, CDecl

def booleanLaw : MLaw := ⟨.le (.get 5 (.tup (.var 18) (.var 1000080))) (.const 1), some 18⟩
def agreementLaw : MLaw := ⟨
 .or (.not (.and (.and (.and (.and trueC trueC) trueC) trueC)
   (.and (.eq (.get 5 (.tup (.var 20) (.var 21))) (.const 1))
     (.eq (.get 5 (.tup (.var 22) (.var 23))) (.const 1)))))
  (.eq (.var 21) (.var 23)), some 20⟩
def claim (e : SEntry) : MLaw × List Nat := (e.law,e.keys2)
def booleanClaim : MLaw × List Nat := (booleanLaw,[1000080])
def agreementClaim : MLaw × List Nat := (agreementLaw,[21,22,23])

theorem boolean_holds {e : SEntry} {ρ M}
 (hl : e.law = booleanLaw) (hk : e.keys2 = [1000080])
 (h : e.Holds ρ (withCnt PaxosEprTarget.declarations ρ M)) :
 ∀ r v, M 5 (cpair r v) ≤ 1 := by
 have hw : holdsOver booleanLaw (withCnt PaxosEprTarget.declarations ρ M) [1000080] ρ := by
  simpa only [SEntry.Holds,hl,hk] using h
 intro r v
 have hh := hw v r
 simpa [booleanLaw,evalC,evalE,upd,withCnt,PaxosEprTarget.declarations,lookup] using hh

theorem agreement_holds {e : SEntry} {ρ M}
 (hl : e.law = agreementLaw) (hk : e.keys2 = [21,22,23])
 (hb : ∀ r v, M 5 (cpair r v) ≤ 1)
 (h : e.Holds ρ (withCnt PaxosEprTarget.declarations ρ M)) : Agreement M := by
 have hw : holdsOver agreementLaw (withCnt PaxosEprTarget.declarations ρ M) [21,22,23] ρ := by
  simpa only [SEntry.Holds,hl,hk] using h
 intro r r' v v' h1 h2
 have b1 := hb r v
 have b2 := hb r' v'
 have c1 : M 5 (cpair r v) = 1 := by omega
 have c2 : M 5 (cpair r' v') = 1 := by omega
 have hh := hw v r' v' r
 simpa [agreementLaw,trueC,evalC,evalE,upd,withCnt,PaxosEprTarget.declarations,lookup,c1,c2] using hh

/-- Both claims must occur in the SAME completely checked counted family.
Neither an individual checkMC nor a native Boolean receipt is substituted. -/
theorem family_agreement (ps : List CEntry)
 (hc : checkCMachine PaxosEprTarget.machine PaxosEprTarget.declarations ps = true)
 (hb : booleanClaim ∈ ps.map (fun ce => claim ce.e))
 (ha : agreementClaim ∈ ps.map (fun ce => claim ce.e)) :
 ∀ ρ M, CReach PaxosEprTarget.machine PaxosEprTarget.declarations ρ M → Agreement M := by
 obtain ⟨b,memB,eqB⟩ := List.mem_map.mp hb
 obtain ⟨a,memA,eqA⟩ := List.mem_map.mp ha
 intro ρ M hr
 have all := cmachine_sound PaxosEprTarget.machine PaxosEprTarget.declarations ps hc ρ M hr
 have bit := boolean_holds (congrArg Prod.fst eqB) (congrArg Prod.snd eqB) (all b memB)
 exact agreement_holds (congrArg Prod.fst eqA) (congrArg Prod.snd eqA) bit (all a memA)

/-- The frozen tree-lane recipe is the EXACT simulated target, not merely
another machine with an informally similar protocol. -/
theorem frozen_machine_exact : PaxosEprTreeRepairChecks.targetMachine.toOption = some PaxosEprTarget.machine := by decide +kernel
theorem frozen_declarations_exact : PaxosEprTreeRepairChecks.targetDecls.toOption = some PaxosEprTarget.declarations := by decide +kernel

def frozenClaims : Bool := match PaxosEprTreeRepairChecks.targetEntries with
 | .ok es => decide (booleanClaim ∈ es.map claim ∧ agreementClaim ∈ es.map claim)
 | .error _ => false

theorem frozen_claims : frozenClaims = true := by decide +kernel

/-- Final source safety gate. The missing input is explicitly the full
checkCMachine theorem for a family whose entries equal the frozen recipe.
There are no missing simulation, cardinality, or public-law premises. -/
theorem source_from_checked_family (ps : List CEntry)
 (hc : checkCMachine PaxosEprTarget.machine PaxosEprTarget.declarations ps = true)
 (he : PaxosEprTreeRepairChecks.targetEntries = .ok (ps.map (·.e))) :
 ∀ ρ M, CReach PaxosEprAtomicSource.machine PaxosEprAtomicSource.declarations ρ M →
  PaxosEprAtomicSource.safety.Holds ρ (withCnt PaxosEprAtomicSource.declarations ρ M) := by
 have claims := frozen_claims
 unfold frozenClaims at claims
 rw [he] at claims
 have hclaims := of_decide_eq_true claims
 simp only [List.map_map,Function.comp_def] at hclaims
 intro ρ M hr
 exact source_safety_from_target (family_agreement ps hc hclaims.1 hclaims.2) hr

#print axioms boolean_holds
#print axioms agreement_holds
#print axioms family_agreement
#print axioms frozen_machine_exact
#print axioms frozen_declarations_exact
#print axioms frozen_claims
#print axioms source_from_checked_family
end Bapa.PaxosEprSafetyGate
