import Kernel
open Cert Kern
namespace PaxosLaw20
-- Synthetic UNSAT goal, not a machine law and not a false-law mutant.
-- The TypeScript source wraps tinyAtom in a singleton `or`; the emitter erases it.
def tinyAtom : C := .lt (.var 0) (.var 1)
def tinyRow : Row := sp [(0,1),(1,-1)] 1
def tinyGoal : Goal := ⟨[.var 0,.var 1], [tinyAtom,.not tinyAtom]⟩
def retainedTinyTree : Tree := .split tinyRow
  (.leafAt [(lconst 1,.fact 1)] [.input 0] [] [])
  (.leafAt [(lconst 1,.fact 0)] [.input 0] [] [])
def correctedTinyTree : Tree := .split tinyRow
  (.leafAt [(lconst 1,.fact 1)] [.input 0] [] [])
  (.leafAt [(tinyRow,.fact 0),(flip tinyRow,.atom 0)] [.input 0,.input 1,.combine 0 1 1 1] [] [])
-- Kernel-reduced proofs of the exact failure and separately supplied control.
theorem retained_tiny_rejected : checkGoal tinyGoal retainedTinyTree = false := by decide
theorem corrected_tiny_accepted : checkGoal tinyGoal correctedTinyTree = true := by decide
-- This is a genuine semantic theorem, not merely a Boolean comparison.
theorem tiny_unsatisfiable (env : Nat → Nat) (maps : Nat → Nat → Nat) :
    ¬ ∀ c ∈ tinyGoal.hyps, evalC env maps c = true :=
  sound tinyGoal correctedTinyTree corrected_tiny_accepted env maps
-- The singleton disjunction's semantic elimination is valid.
theorem singleton_or_equivalent (c : C) (env : Nat → Nat) (maps : Nat → Nat → Nat) :
    [evalC env maps c].any id = evalC env maps c := by simp
-- The constant contradiction row is sound whenever the source atom holds and its split is false.
theorem derived_contradiction (a b : Nat) (ha : a < b)
    (hp : ¬ ((a : Int) - (b : Int) + 1 ≤ 0)) : False := by omega
#print axioms retained_tiny_rejected
#print axioms corrected_tiny_accepted
#print axioms singleton_or_equivalent
#print axioms derived_contradiction
#print axioms tiny_unsatisfiable
end PaxosLaw20
