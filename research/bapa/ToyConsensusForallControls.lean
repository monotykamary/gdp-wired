import ToyConsensusForallTransport

namespace Bapa.ToyConsensusForallControls
open Kern
open Bapa.ToyConsensusForallTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The full target check starts each tree at the empty path. No deleted
    z<64 branch condition is passed to the surviving subtree. -/
def obligationChecks : List Bool := proof.flatMap fun e =>
  [checkMC (cStartGoal machine declarations e.e) (cStartDecls machine declarations) e.start,
   checkMC (cStepGoal machine declarations (proof.map CEntry.e) e.e)
     (cStepDecls machine declarations) e.step]

theorem all_sixteen_checks : obligationChecks = List.replicate 16 true := by decide +kernel

def hasBoundRow : Tree → Bool
  | .split _ a b => hasBoundRow a || hasBoundRow b
  | .leaf rows _ _ _ => rows.any fun r => (CertificateBoundErasure.erasedSplit 64 r).isSome
  | .leafAt rows _ _ _ => rows.any fun r => (CertificateBoundErasure.erasedSplit 64 r.1).isSome
  | .leafSq rows _ _ _ _ => rows.any fun r => (CertificateBoundErasure.erasedSplit 64 r.1).isSome

theorem no_surviving_bound_rows :
    proof.all (fun e => !hasBoundRow e.start.tree && !hasBoundRow e.step.tree) = true := by
  decide +kernel

/-- Append the old value-column-7 < 64 requirement to a surviving leaf.
    Appending retains every existing input row index and proof step. -/
def requireOldBound : Tree → Tree
  | .split r a b => .split r (requireOldBound a) b
  | .leaf rows steps eqs prods =>
    .leaf (rows ++ [sp [(7, 1)] (-63)]) steps eqs prods
  | .leafAt rows steps eqs prods =>
    .leafAt (rows ++ [(sp [(7, 1)] (-63), .fact 21)]) steps eqs prods
  | .leafSq rows sqs steps eqs prods =>
    .leafSq (rows ++ [(sp [(7, 1)] (-63), .fact 21)]) sqs steps eqs prods

def safetyEntry : CEntry := proof[2]'(by decide +kernel)
def badEntry : CEntry := {safetyEntry with
  step := {safetyEntry.step with tree := requireOldBound safetyEntry.step.tree}}

def badProof : List CEntry := proof.zipIdx.map fun (e, i) => if i = 2 then badEntry else e

theorem surviving_old_bound_refused :
    checkMC (cStepGoal machine declarations (proof.map CEntry.e) badEntry.e)
      (cStepDecls machine declarations) badEntry.step = false := by decide +kernel

theorem surviving_old_bound_family_refused :
    checkCMachine machine declarations badProof = false := by decide +kernel

theorem count_definitions_unchanged :
    declarations = captured_toy_consensus_forall_0_decls := rfl

theorem request_semantics_unchanged (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    sView machine ρ M ι κ = sView captured_toy_consensus_forall_0_machine ρ M ι κ := rfl

theorem step_semantics_unchanged (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (ι : Nat → Nat) (κ : Nat → Nat → Nat) :
    sNext machine ρ M ι κ = sNext captured_toy_consensus_forall_0_machine ρ M ι κ := rfl

#eval do
  IO.println s!"all16={obligationChecks == List.replicate 16 true}"
  IO.println s!"no-surviving-bound-rows={proof.all (fun e => !hasBoundRow e.start.tree && !hasBoundRow e.step.tree)}"
  IO.println s!"mutant-step-accepted={checkMC (cStepGoal machine declarations (proof.map CEntry.e) badEntry.e) (cStepDecls machine declarations) badEntry.step}"
  IO.println s!"mutant-family-accepted={checkCMachine machine declarations badProof}"

#print axioms all_sixteen_checks
#print axioms no_surviving_bound_rows
#print axioms surviving_old_bound_refused
#print axioms surviving_old_bound_family_refused
#print axioms count_definitions_unchanged
#print axioms request_semantics_unchanged
#print axioms step_semantics_unchanged
end Bapa.ToyConsensusForallControls
