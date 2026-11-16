import CertificateBoundSubstitution
open Kern Bapa.CertificateBoundSubstitution
namespace TypedControls
-- Identical numeric cutoff does not equate two symbolic domains.
def distinctTyping : Typed.Typing := ⟨[10,11], [(0,10),(1,11)], []⟩
def table : List VDef := [.var 0, .var 1]
def swappedTyping : Typed.Typing := ⟨[10,11], [(0,11),(1,10)], []⟩
theorem independently_typed : Typed.condition 64 distinctTyping (.lt (.var 0) (.const 64)) = some (.lt (.var 0) (.var 10)) := by decide +kernel
theorem swap_not_equivalent : Typed.condition 64 distinctTyping (.lt (.var 0) (.const 64)) ≠ Typed.condition 64 swappedTyping (.lt (.var 0) (.const 64)) := by decide +kernel
def independentEnv (i : Nat) : Nat := if i = 0 then 2 else if i = 10 then 1 else if i = 11 then 3 else 0
theorem wrong_sort_is_false : evalC independentEnv (fun _ _ => 0) (.lt (.var 0) (.var 10)) = false ∧ evalC independentEnv (fun _ _ => 0) (.lt (.var 0) (.var 11)) = true := by decide +kernel
theorem row_keeps_independent_parameter : Typed.boundRow 64 distinctTyping table (sp [(0,1)] (-63)) = some (sp [(0,-1),(2,1)] 1) := by rfl
#print axioms TypedControls.independently_typed
#print axioms TypedControls.swap_not_equivalent
#print axioms TypedControls.wrong_sort_is_false
#print axioms TypedControls.row_keeps_independent_parameter
end TypedControls
