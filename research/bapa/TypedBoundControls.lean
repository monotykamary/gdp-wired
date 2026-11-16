import CertificateBoundSubstitution
open Kern Bapa.CertificateBoundSubstitution
namespace TypedBoundControls
def typing : Typed.Typing := ⟨[100,101,102,103], [(1,100),(2,101)], [(7,101),(9,100)]⟩
def table : List VDef := [.var 1, .var 2, .cellT 7 [], .cellT 9 [], .var 99]
theorem node_row : Typed.boundRow 64 typing table (sp [(0,1)] (-63)) = some (sp [(0,-1),(4,1)] 1) := by rfl
theorem request_row : Typed.boundRow 64 typing table (sp [(1,1)] (-63)) = some (sp [(1,-1),(5,1)] 1) := by rfl
theorem request_ghost : Typed.boundRow 64 typing table (sp [(2,1)] (-63)) = some (sp [(1,-1),(6,1)] 1) := by rfl
theorem node_ghost : Typed.boundRow 64 typing table (sp [(3,1)] (-63)) = some (sp [(0,-1),(7,1)] 1) := by rfl
theorem unknown_refused : Typed.boundRow 64 typing table (sp [(4,1)] (-63)) = none := by decide +kernel
theorem expression_sort : Typed.condition 64 typing (.lt (.get 7 (.var 1)) (.const 64)) = some (.lt (.get 7 (.var 1)) (.var 101)) := by decide +kernel
#print axioms node_row
#print axioms request_row
#print axioms request_ghost
#print axioms node_ghost
#print axioms unknown_refused
#print axioms expression_sort
end TypedBoundControls
