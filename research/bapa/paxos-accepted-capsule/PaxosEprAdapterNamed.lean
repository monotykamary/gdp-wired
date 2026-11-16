import PaxosEprAdapterCertificate

/-! Reconstruct named hypotheses by their retained generated-goal origin.
The tuple-binder translator moves packed single instances after scalar singles;
we account for exactly that permutation. No hypothesis is discarded, inserted,
or replaced by an arbitrary equivalent formula. This is a candidate only: the
unchanged full checkMC must still validate every leaf and counted side condition. -/
namespace Bapa.PaxosEprAdapterNamed
open Kern PaxosEprAdapterSyntax

def singleOrder (profiles : List (Nat × Nat)) (xs : List (Nat × E)) : List Nat :=
  let packed := fun p : (Nat × E) × Nat => profiles.any (fun q => q.1 == p.1.1)
  ((xs.zipIdx.filter (fun p => !packed p)) ++ xs.zipIdx.filter packed).map (·.2)

def goalOrder (profiles : List (Nat × Nat))
    (oldS newS : SMachine) (oldPs newPs : List SEntry) (oldE newE : SEntry)
    (oldGoal newGoal : List C) (step : Bool) : Except Error (List Nat) := do
  if oldGoal.length != newGoal.length then
    throw (.field "hyps" (.table 0 "generated goal length changed"))
  if !step then return List.range oldGoal.length
  let oldPrefix := 1 + (factHyps oldS oldE.finsts oldE.pfinsts).length +
    (scalarHyps (sLaws oldPs oldE.pinsts)).length
  let newPrefix := 1 + (factHyps newS newE.finsts newE.pfinsts).length +
    (scalarHyps (sLaws newPs newE.pinsts)).length
  let oldBlock := instHyps (sLaws oldPs oldE.pinsts) (sInsts oldPs oldE.insts oldE.pinsts)
  let newBlock := instHyps (sLaws newPs newE.pinsts) (sInsts newPs newE.insts newE.pinsts)
  if oldPrefix != newPrefix || oldBlock.length != oldE.insts.length + oldE.pinsts.length ||
      newBlock.length != oldBlock.length then
    throw (.field "hyps" (.table 0 "instance origin shape changed"))
  let order := singleOrder profiles oldE.insts
  let expected := order.filterMap (fun i => oldE.insts[i]?)
  let actualIds := newE.insts.map (·.1) ++ (newE.pinsts.take (order.length-newE.insts.length)).map (·.1)
  if expected.map (·.1) != actualIds then
    throw (.field "hyps" (.table 0 "instance identity permutation changed"))
  (List.range oldGoal.length).mapM fun j => do
    if oldPrefix <= j && j < oldPrefix + oldE.insts.length then
      match order.zipIdx.find? (fun p => p.1 == j-oldPrefix) with
      | some (_,n) => return newPrefix+n
      | none => throw (.field "hyps" (.table j "instance origin missing"))
    else return j

def reconstruct (oldGoal newGoal : List C) (order : List Nat)
    (hyps : List C) : Except Error (List C) :=
  hyps.zipIdx.mapM fun (h,i) => atField s!"hyps[{i}]" do
    let some (_,origin) := oldGoal.zipIdx.find? (fun p => beqC p.1 h)
      | throw (.table i "retained named hypothesis has no generated origin")
    let some index := order[origin]?
      | throw (.table i "target origin index missing")
    let some actual := newGoal[index]?
      | throw (.table i "target generated hypothesis missing")
    return actual

def hypotheses (profiles : List (Nat × Nat))
    (oldS newS : SMachine) (oldDs newDs : List CDecl)
    (oldPs newPs : List SEntry) (oldE newE : SEntry) (step : Bool) (k : CCert) :
    Except Error (List C) := do
  let oldGoal := if step then cStepGoal oldS oldDs oldPs oldE else cStartGoal oldS oldDs oldE
  let newGoal := if step then cStepGoal newS newDs newPs newE else cStartGoal newS newDs newE
  let order ← goalOrder profiles oldS newS oldPs newPs oldE newE oldGoal newGoal step
  reconstruct oldGoal newGoal order k.hyps

def certificate (cfg : Config) (profiles : List (Nat × Nat))
    (oldS newS : SMachine) (oldDs newDs : List CDecl)
    (oldPs newPs : List SEntry) (oldE newE : SEntry) (step : Bool) (k : CCert) :
    Except Error CCert := do
  let hs ← hypotheses profiles oldS newS oldDs newDs oldPs newPs oldE newE step k
  PaxosEprAdapterCertificate.certificate cfg k (some hs)

theorem permutation_control :
    singleOrder [(3,2)] [(3,.var 8),(1,.var 9),(3,.var 10)] = [1,0,2] := by decide +kernel

theorem named_order_and_duplicates_kept :
    (reconstruct [(.eq (.var 1) (.const 0)),(.eq (.var 2) (.const 0))]
      [(.eq (.var 3) (.const 0)),(.eq (.var 4) (.const 0))] [1,0]
      [(.eq (.var 2) (.const 0)),(.eq (.var 1) (.const 0)),(.eq (.var 2) (.const 0))]).toOption =
        some [(.eq (.var 3) (.const 0)),(.eq (.var 4) (.const 0)),(.eq (.var 3) (.const 0))] := by decide +kernel

theorem missing_origin_refused :
    (reconstruct [] [trueC] [] [trueC]).toOption = none := by decide +kernel

#print axioms permutation_control
#print axioms named_order_and_duplicates_kept
#print axioms missing_origin_refused
end Bapa.PaxosEprAdapterNamed
