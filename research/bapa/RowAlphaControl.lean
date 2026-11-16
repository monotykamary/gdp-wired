import RowAlpha
namespace Kern.RowAlpha.Control
def r : Rename := ⟨0, 1, 2⟩
def bad (s : SMachine) : SMachine := { s with every := [(0, 1, .var 2)] }
def target (s : SMachine) : SMachine := { s with every := [(0, 2, .var 2)] }
def good (s : SMachine) : SMachine := { s with every := [(0, 1, .var 1)] }
def rho (i : Nat) : Nat := if i = 2 then 1 else 0
def maps (_ _ : Nat) : Nat := 0
example (s : SMachine) : valid (bad s) r = false := by rfl
example (s : SMachine) : rename (bad s) r = target s := by rfl
example (s : SMachine) : everyMaps (bad s) rho maps 0 0 = 1 := by rfl
example (s : SMachine) : everyMaps (target s) rho maps 0 0 = 0 := by rfl
example (s : SMachine) : valid (good s) r = true := by rfl
example (s : SMachine) : everyMaps (good s) rho maps 0 0 = 0 := by rfl
example (s : SMachine) : everyMaps (rename (good s) r) rho maps 0 0 = 0 := by rfl
example (s : SMachine) : Equiv (renameAll (good s) [r]) (good s) := by
  apply renameAll_equiv
  rfl
#print axioms Kern.RowAlpha.renameAll_equiv
#print axioms Kern.RowAlpha.Equiv.creach_imp
#print axioms Kern.RowAlpha.Equiv.sreach_imp
end Kern.RowAlpha.Control
