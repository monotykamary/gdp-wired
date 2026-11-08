import CountMachine

/- Executable checks of the Lean rule. These use kernel reduction, not native_decide. -/
namespace Kern.LemmaCutExamples
open Cert

private def tab : List VDef := [.var 0, .var 1, .var 2]
private def ab : Row := ⟨[(0, 1), (1, -1)], 0⟩
private def b0 : Row := ⟨[(1, 1)], 0⟩
private def a0 : Row := ⟨[(0, 1)], 0⟩
private def c0 : Row := ⟨[(2, 1)], 0⟩
private def hyps : List C := [.le (.var 0) (.var 1), .le (.var 1) (.const 0),
  .lt (.const 0) (.var 0), .le (.var 2) (.const 0)]
private def goal : Goal := ⟨tab, hyps⟩
private def pair (a b : Row) : Tree :=
  .leaf [a, b] [.input 0, .input 1, .combine 0 1 1 1] [] []
private def derived : Tree :=
  .leaf [ab, b0, flip a0] [.input 0, .input 1, .input 2, .combine 0 1 1 1, .combine 3 2 1 1] [] []
private def entry : CutLemma := ⟨[c0], a0, derived, some [0, 1]⟩
private def main : Tree := .split c0 (pair a0 (flip a0)) (pair c0 (flip c0))

-- A nontrivial summed row can be shared below its declared decision point.
example : checkGoalLemmas goal main [entry] = true := by decide +kernel
example : checkGoal goal main = false := by decide +kernel
example : checkCounted ⟨hyps, []⟩ [] tab main [entry] = true := by decide +kernel

-- A legacy certificate payload defaults to no lemmas.
private def legacy : CCert := {hyps, reads := [], insts := [], tab, tree := derived, picks := []}
example : legacy.lemmas = [] := rfl
example : checkMC hyps [] legacy = true := by decide +kernel
private def counted : CCert := {legacy with tree := main, lemmas := [entry]}
example : checkMC hyps [] counted = true := by decide +kernel

-- The condition is not decided at the root. A cut cannot be cited above its decision.
example : checkGoalLemmas goal (pair a0 (flip a0)) [entry] = false := by decide +kernel
-- Nor can it be cited on the opposite side of the decision.
example : checkGoalLemmas goal main [{entry with when := [flip c0]}] = false := by decide +kernel
-- A proof is checked against exactly its declared source slice, never another slice or its caller's rows.
example : checkGoalLemmas goal main [{entry with slice := some [0, 3]}] = false := by decide +kernel
example : checkGoalLemmas goal main [{entry with slice := some [0, 40]}] = false := by decide +kernel
-- An empty/non-refuting lemma proof is rejected even when the main tree could use its conclusion.
example : checkGoalLemmas goal main [{entry with tree := .leaf [] [] [] []}] = false := by decide +kernel
-- A lemma cannot use its own claimed conclusion as an input row.
example : checkGoalLemmas goal main [{entry with tree := pair a0 (flip a0)}] = false := by decide +kernel

end Kern.LemmaCutExamples

#print axioms Kern.lemma_sound
#print axioms Kern.goalLemmas_sound
#print axioms Kern.counted_sound
#print axioms Kern.countedW_sound
#print axioms Kern.mc_sound
#print axioms Kern.cmachine_sound
