import CertificateBoundErasure

/-! Search-free replay reporting. Every result, including a refusal, is checked
again in Lean. Candidate transformation is not an unconditional transport theorem. -/
namespace Bapa.BoundErasureReplay
open Kern
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked_plain_transport (bound : Nat) (s : SMachine) (ps : List SEntry)
    (h : checkSMachine (CertificateBoundErasure.machine bound s)
      (ps.map (CertificateBoundErasure.entry bound)) = true) :
    ∀ ρ M, SReach (CertificateBoundErasure.machine bound s) ρ M →
      ∀ e ∈ ps.map (CertificateBoundErasure.entry bound), e.Holds ρ M :=
  smachine_sound _ _ h

def sourceName : Src → String
  | .atom i => s!"atom:{i}"
  | .fact i => s!"fact:{i}"
  | .nat i => s!"nat:{i}"
  | .eq i => s!"eq:{i}"
  | .term i => s!"term:{i}"
  | .any => "any"

def firstFailure (tab : List VDef) (hyps : List C) : Path → Tree → Option String
  | path, .split r yes no =>
    match firstFailure tab hyps ((r, true) :: path) yes with
    | some s => some ("Y" ++ s)
    | none => (firstFailure tab hyps ((r, false) :: path) no).map ("N" ++ ·)
  | path, .leaf rows steps eqs prods =>
    if leafOk tab path hyps rows steps eqs prods then none
    else some s!":unhinted-leaf rows={repr rows} steps={repr steps}"
  | path, .leafAt rows steps eqs prods =>
    if leafAtOk tab path hyps rows steps eqs prods then none else
      some (":" ++ String.intercalate ";" (rows.zipIdx.filterMap fun (r, i) =>
        if (srcRows tab path hyps eqs r.2).any (same r.1) ||
            (leafRows tab path hyps eqs).any (same r.1) then none
        else some s!"row{i} {sourceName r.2} {repr r.1}") ++
        s!"; arithmetic={Cert.check (rows.map (·.1)) steps}; steps={repr steps}")
  | path, .leafSq rows sqs steps eqs prods =>
    if leafSqOk tab path hyps rows sqs steps eqs prods then none else some ":square-leaf"

def requireOldBound (column : Nat) : Tree → Tree
  | .split r a b => .split r (requireOldBound column a) b
  | .leaf rows steps eqs prods =>
    .leaf (rows ++ [sp [(column, 1)] (-63)]) steps eqs prods
  | .leafAt rows steps eqs prods =>
    .leafAt (rows ++ [(sp [(column, 1)] (-63), .any)]) steps eqs prods
  | .leafSq rows sqs steps eqs prods =>
    .leafSq (rows ++ [(sp [(column, 1)] (-63), .any)]) sqs steps eqs prods

def boundMutant (e : SEntry) (column : Nat := 1) : SEntry :=
  {e with step := (e.step.1, e.step.2.1, requireOldBound column e.step.2.2)}

def plainChecks (s : SMachine) (ps : List SEntry) : List Bool :=
  ps.flatMap fun e => [checkIn (sStartGoal s e) e.start, checkIn (sStepGoal s ps e) e.step]

def plainDiagnostic (goal : List C) (k : Kern.Cert) : String :=
  let hyps := if k.2.1.isEmpty then goal else k.2.1
  let named := k.2.1.isEmpty || namedIn goal k.2.1 goal
  s!"named={named};table={wfTab 0 k.1};first-failure={firstFailure k.1 hyps [] k.2.2}"

/-- Emit observations and a second module proving the exact observed Boolean
values. Successful families alone receive a reachability theorem. -/
def emitPlain (out importName ns : String) (s : SMachine) (ps : List SEntry)
    (mutantColumn : Nat := 1) : IO Unit := do
  let checks := plainChecks s ps
  let family := checkSMachine s ps
  let mut rows : List String := ["law\tphase\tchecked"]
  for (e,i) in ps.zipIdx do
    let start := checkIn (sStartGoal s e) e.start
    let step := checkIn (sStepGoal s ps e) e.step
    rows := rows ++ [s!"{i}\tinit\t{start}",s!"{i}\tstep\t{step}"]
    if !start then rows := rows ++ [s!"diagnostic\t{i}:init\t{plainDiagnostic (sStartGoal s e) e.start}"]
    if !step then rows := rows ++ [s!"diagnostic\t{i}:step\t{plainDiagnostic (sStepGoal s ps e) e.step}"]
  rows := rows ++ [s!"family\tall\t{family}"]
  let text := String.intercalate "\n" rows ++ "\n"
  IO.println text
  IO.FS.writeFile (out ++ "/checks.tsv") text
  let mut proofText := s!"import {importName}\nopen Kern\nnamespace {ns}.Checked\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
  let vals := String.intercalate ", " (checks.map toString)
  proofText := proofText ++ s!"theorem obligations : Bapa.BoundErasureReplay.plainChecks {ns}.machine {ns}.proof = [{vals}] := by decide +kernel\n#print axioms obligations\n"
  proofText := proofText ++ s!"theorem family : checkSMachine {ns}.machine {ns}.proof = {family} := by decide +kernel\n#print axioms family\n"
  if family then
    proofText := proofText ++ s!"theorem laws : ∀ ρ M, SReach {ns}.machine ρ M → ∀ e ∈ {ns}.proof, e.Holds ρ M := smachine_sound _ _ family\n#print axioms laws\n"
  match ps.head? with
  | none => pure ()
  | some e =>
    let bad := boundMutant e mutantColumn
    let refused := !(checkIn (sStepGoal s ps bad) bad.step)
    IO.println s!"surviving-bound-mutant-refused={refused}"
    if !refused then throw (IO.userError "surviving-bound mutant was accepted")
    proofText := proofText ++ s!"def first : SEntry := {ns}.proof[0]'(by decide +kernel)\ndef bad : SEntry := Bapa.BoundErasureReplay.boundMutant first {mutantColumn}\ntheorem surviving_bound_refused : checkIn (sStepGoal {ns}.machine {ns}.proof bad) bad.step = false := by decide +kernel\n#print axioms surviving_bound_refused\n"
  proofText := proofText ++ s!"end {ns}.Checked\n"
  IO.FS.writeFile (out ++ "/Checks.lean") proofText

#print axioms checked_plain_transport
end Bapa.BoundErasureReplay
