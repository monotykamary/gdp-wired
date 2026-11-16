import BoundErasureReplay

/-! A deterministic Boolean cleanup after bound erasure. No SAT/SMT solver,
invariant enumeration, arithmetic proof search, or invented assumption is used.
A rejected leaf is replaced ONLY when the target kernel's own leafRows already
contains a positive constant row. The complete checker must still accept the
resulting tree, including all equal-cell side conditions. -/
namespace Bapa.CertificateBooleanCleanup
open Kern

def closeLeaf (tab : List VDef) (hyps : List C) (path : Path)
    (eqs : List (Nat × Nat)) (original : Tree) : Tree :=
  if checkT tab hyps path original then original else
    match (leafRows tab path hyps eqs).find? (fun r => Cert.allZero r.coefs && decide (0 < r.const)) with
    | none => original
    | some r => .leafAt [(r,.any)] [.input 0] eqs []

def tree (tab : List VDef) (hyps : List C) : Path → Tree → Tree
  | path, .split row yes no => .split row
      (tree tab hyps ((row,true)::path) yes) (tree tab hyps ((row,false)::path) no)
  | path, t@(.leaf _ _ eqs _) => closeLeaf tab hyps path eqs t
  | path, t@(.leafAt _ _ eqs _) => closeLeaf tab hyps path eqs t
  | path, t@(.leafSq _ _ _ eqs _) => closeLeaf tab hyps path eqs t

def certificate (goal : List C) (k : Kern.Cert) : Kern.Cert :=
  let hyps := if k.2.1.isEmpty then goal else k.2.1
  (k.1,k.2.1,tree k.1 hyps [] k.2.2)

def entry (s : SMachine) (ps : List SEntry) (e : SEntry) : SEntry :=
  {e with
    start := certificate (sStartGoal s e) e.start
    step := certificate (sStepGoal s ps e) e.step}

theorem named_hypotheses_unchanged (goal : List C) (k : Kern.Cert) :
    (certificate goal k).2.1 = k.2.1 := rfl

theorem table_unchanged (goal : List C) (k : Kern.Cert) :
    (certificate goal k).1 = k.1 := rfl

#print axioms named_hypotheses_unchanged
#print axioms table_unchanged
end Bapa.CertificateBooleanCleanup
