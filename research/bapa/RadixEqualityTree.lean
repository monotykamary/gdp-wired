import RadixCertificateTable
import CertificateBoundErasure

/-! Replace recognized two-sided packed-address equality tests by component
comparisons. This is a deterministic certificate candidate transformation,
NOT an assertion that integer ordering of packed keys survives unbounded
re-keying. Every resulting branch and arithmetic leaf is rechecked by Kern.
No new premise, arithmetic search, or invariant is introduced. -/
namespace Bapa.RadixEqualityTree
open Kern

structure Plan where
  old : Cert.Row
  components : List Cert.Row

/-- Obtain tuple equality plans only from matching old/new cell columns. -/
def plans (shift : Nat) (oldTab newTab : List VDef) : List Plan :=
  (List.range oldTab.length).flatMap fun i =>
    (List.range oldTab.length).filterMap fun j =>
      match oldTab[i]?, oldTab[j]?, newTab[i+shift]?, newTab[j+shift]? with
      | some (VDef.cell m a), some (VDef.cell n b), some (VDef.cellT m' as_), some (VDef.cellT n' bs) =>
        if m == n && m == m' && n == n' && as_.length == bs.length &&
            as_.length > 1 && !(same a b) then
          some ⟨lsub a b,(as_.zip bs).map (fun (x,y) => lsub x y)⟩
        else none
      | _, _, _, _ => none

/-- A context changes exactly scalar multiples of one old comparison's
coefficient vector. Its constant offset is preserved. This merely proposes
leaf rows; the new leaf checker still has to find every proposed premise. -/
def rewriteOne (p : Plan) (replacement r : Cert.Row) : Option Cert.Row := do
  let (j,c) ← p.old.coefs.find? (fun q => q.2 != 0)
  let a := ((r.coefs.find? (fun q => q.1 == j)).map (·.2)).getD 0
  if a % c != 0 then none else
    let factor := a / c
    if Cert.allZero (lsub r (lscale factor p.old)).coefs then
      some (ladd (lscale factor replacement) (lconst (r.const-factor*p.old.const)))
    else none

def row (shift : Nat) (contexts : List (Plan × Cert.Row)) (r : Cert.Row) : Cert.Row :=
  match contexts.findSome? (fun (p,replacement) => rewriteOne p replacement r) with
  | some r' => r'
  | none => RadixCertificateTable.row shift r

def step (shift : Nat) (contexts : List (Plan × Cert.Row)) : Cert.Step → Cert.Step
  | .cut i g q c => let r := row shift contexts ⟨q,c⟩; .cut i g r.coefs r.const
  | s => s

/-- Componentwise equality is the conjunction of both non-strict comparisons
for each component. All negative/positive branches remain present. -/
def componentCases (equal : Tree) (negative positive : Cert.Row → Tree) : List Cert.Row → Tree
  | [] => equal
  | r :: rs => .split r
      (.split (lscale (-1) r) (componentCases equal negative positive rs) (negative r))
      (positive r)

def tree (shift : Nat) (bound : Option Nat) (ps : List Plan)
    (contexts : List (Plan × Cert.Row)) : Tree → Tree
  | .split r yes no =>
    match bound.bind (fun n => CertificateBoundErasure.erasedSplit n r) with
    | some true => tree shift bound ps contexts yes
    | some false => tree shift bound ps contexts no
    | none =>
      match hyes : yes, ps.find? (fun p => same p.old r) with
      | .split opposite equal negative, some plan =>
        if same opposite (lscale (-1) r) then
          componentCases
            (tree shift bound ps ((plan,lconst 0)::contexts) equal)
            (fun component => tree shift bound ps ((plan,component)::contexts) negative)
            (fun component => tree shift bound ps ((plan,component)::contexts) no)
            plan.components
        else .split (row shift contexts r)
          (tree shift bound ps contexts yes) (tree shift bound ps contexts no)
      | _, _ => .split (row shift contexts r)
          (tree shift bound ps contexts yes) (tree shift bound ps contexts no)
  | .leaf rs ss eqs prods =>
    .leaf (rs.map (row shift contexts)) (ss.map (step shift contexts))
      (RadixCertificateTable.pairs shift eqs) prods
  | .leafAt rs ss eqs prods =>
    .leafAt (rs.map (fun (r,s) => (row shift contexts r,RadixCertificateTable.source shift s)))
      (ss.map (step shift contexts)) (RadixCertificateTable.pairs shift eqs) prods
  | .leafSq rs sqs ss eqs prods =>
    .leafSq (rs.map (fun (r,s) => (row shift contexts r,RadixCertificateTable.source shift s)))
      (sqs.map (row shift contexts)) (ss.map (step shift contexts))
      (RadixCertificateTable.pairs shift eqs) prods
termination_by t => sizeOf t
decreasing_by all_goals simp_all <;> omega

/-- Only the complete trusted checker can turn candidate syntax into a law. -/
theorem checked_family (s : SMachine) (ps : List SEntry)
    (h : checkSMachine s ps = true) :
    ∀ ρ M, SReach s ρ M → ∀ e ∈ ps, e.Holds ρ M := smachine_sound _ _ h

#print axioms checked_family
end Bapa.RadixEqualityTree
