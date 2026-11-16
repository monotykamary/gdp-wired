import Proofs
import CertificateBoundErasure

namespace Bapa.ToyConsensusForallTransport
open Kern
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def machine := CertificateBoundErasure.machine 64 captured_toy_consensus_forall_0_machine
def declarations := captured_toy_consensus_forall_0_decls.map (CertificateBoundErasure.countDeclaration 64)
def proof := captured_toy_consensus_forall_0_proof.map (CertificateBoundErasure.countedEntry 64)

#eval do
  IO.println "law\tphase\ttranslated-check"
  for (e, i) in proof.zipIdx do
    IO.println s!"{i}\tinit\t{checkMC (cStartGoal machine declarations e.e) (cStartDecls machine declarations) e.start}"
    IO.println s!"{i}\tstep\t{checkMC (cStepGoal machine declarations (proof.map CEntry.e) e.e) (cStepDecls machine declarations) e.step}"
  IO.println s!"family\tall\t{checkCMachine machine declarations proof}"

theorem no_size_cap : machine.f.m.pre = trueC := by decide +kernel

theorem check : checkCMachine machine declarations proof = true := by decide +kernel

theorem laws : ∀ ρ M, CReach machine declarations ρ M →
    ∀ e ∈ proof, e.e.Holds ρ (withCnt declarations ρ M) :=
  CertificateBoundErasure.checked_counted_transport 64 _ _ _ check

def unprunedProof : List CEntry := captured_toy_consensus_forall_0_proof.map fun e =>
  {CertificateBoundErasure.countedEntry 64 e with
    start := {CertificateBoundErasure.countedCertificate 64 e.start with tree := e.start.tree}
    step := {CertificateBoundErasure.countedCertificate 64 e.step with tree := e.step.tree}}

theorem unpruned_control_rejected :
    checkCMachine machine declarations unprunedProof = false := by decide +kernel

def sourceName : Src → String
  | .atom i => s!"atom:{i}"
  | .fact i => s!"fact:{i}"
  | .nat i => s!"nat:{i}"
  | .eq i => s!"eq:{i}"
  | .term i => s!"term:{i}"
  | .any => "any"

def failedLeaves (tab : List VDef) (hyps : List C) : Path → Tree → List String
  | path, .split row yes no =>
    (failedLeaves tab hyps ((row, true) :: path) yes).map ("Y" ++ ·) ++
      (failedLeaves tab hyps ((row, false) :: path) no).map ("N" ++ ·)
  | path, .leaf rows steps eqs prods =>
    if leafOk tab path hyps rows steps eqs prods then [] else [":unhinted-leaf"]
  | path, .leafAt rows steps eqs prods =>
    if leafAtOk tab path hyps rows steps eqs prods then [] else
      [":" ++ String.intercalate ";" (rows.zipIdx.filterMap fun (r, i) =>
        if (srcRows tab path hyps eqs r.2).any (same r.1) ||
            (leafRows tab path hyps eqs).any (same r.1) then none
        else some s!"row{i} {sourceName r.2} {repr r.1}")]
  | path, .leafSq rows sqs steps eqs prods =>
    if leafSqOk tab path hyps rows sqs steps eqs prods then [] else [":square-leaf"]

def audit (goal : List C) (ds : List CDecl) (k : CCert) : IO Unit := do
  IO.println s!"named={namedIn goal k.hyps goal}, reads={readsOk k.hyps ds k.reads}"
  match toCounts ds k.reads with
  | none => IO.println "toCounts=none"
  | some cs =>
    match countHyps cs k.insts with
    | none => IO.println "countHyps=none"
    | some hs =>
      let full := k.hyps ++ k.reads.map (readHyp ds) ++ pickHyps ds k.reads k.picks ++ hs
      for bad in (failedLeaves k.tab full [] k.tree).take 3 do IO.println bad

#eval do
  for (e, i) in proof.zipIdx do
    IO.println s!"DIAGNOSTIC {i} init"
    audit (cStartGoal machine declarations e.e) (cStartDecls machine declarations) e.start
    IO.println s!"DIAGNOSTIC {i} step"
    audit (cStepGoal machine declarations (proof.map CEntry.e) e.e) (cStepDecls machine declarations) e.step

#print axioms no_size_cap
#print axioms check
#print axioms laws
#print axioms unpruned_control_rejected
end Bapa.ToyConsensusForallTransport
