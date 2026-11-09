import Kernel
open Kern Cert
namespace ExportShape
-- Neutral binary children retain singleton connective row extraction, without changing truth.
def trueC : C := .le (.const 0) (.const 0)
def falseC : C := .lt (.const 0) (.const 0)
theorem singleton_or_eval (env : Nat → Nat) (maps : Nat → Nat → Nat) (c : C) :
    evalC env maps (.or c falseC) = evalC env maps c := by simp [evalC, falseC, evalE]
theorem singleton_and_eval (env : Nat → Nat) (maps : Nat → Nat → Nat) (c : C) :
    evalC env maps (.and c trueC) = evalC env maps c := by simp [evalC, trueC, evalE]
def atom : C := .lt (.var 0) (.var 1)
def row : Row := sp [(0,1),(1,-1)] 1
def originalTree : Tree := .split row
  (.leafAt [(lconst 1,.fact 1)] [.input 0] [] [])
  (.leafAt [(lconst 1,.fact 0)] [.input 0] [] [])
def shapeGoal : Goal := ⟨[.var 0,.var 1], [.or atom falseC,.not atom]⟩
def erasedGoal : Goal := ⟨[.var 0,.var 1], [atom,.not atom]⟩
-- No replacement leaves or arithmetic derivations: the original input-only tree now checks.
theorem shape_preserved_tree : checkGoal shapeGoal originalTree = true := by decide
theorem erased_tree_rejected : checkGoal erasedGoal originalTree = false := by decide
theorem negative_singleton_and : facts [.var 0,.var 1] [(row,true)] false (.and atom trueC) = [lconst 1] := by rfl
theorem source_goal_unsatisfiable (env : Nat → Nat) (maps : Nat → Nat → Nat) :
    ¬ ∀ c ∈ shapeGoal.hyps, evalC env maps c = true := sound _ _ shape_preserved_tree env maps
#print axioms singleton_or_eval
#print axioms singleton_and_eval
#print axioms shape_preserved_tree
#print axioms erased_tree_rejected
#print axioms negative_singleton_and
#print axioms source_goal_unsatisfiable
end ExportShape
