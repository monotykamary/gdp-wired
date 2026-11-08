import CountMachine
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- duplicate_slice; independently expected true in Lean
example : checkGoalLemmas ⟨[.var 0, .var 1, .var 2, .var 3], [.le (.var 0) (.var 1), .le (.var 1) (.const 0), .lt (.const 0) (.var 0), .le (.var 2) (.const 0)]⟩ (.split (sp [(2, 1)] 0)
  (.leafAt [((sp [(0, 1)] 0), .any), ((sp [(0, (-1))] 1), .fact 2)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leafAt [((sp [(2, (-1))] 1), .any), ((sp [(2, 1)] 0), .fact 3)] [.input 1, .input 0, .combine 0 1 1 1] [] [])) [⟨[(sp [(2, 1)] 0)], (sp [(0, 1)] 0), .leafAt [((sp [(0, (-1))] 1), .any), ((sp [(0, 1), (1, (-1))] 0), .fact 0), ((sp [(1, 1)] 0), .fact 2)] [.input 1, .input 2, .input 0, .combine 0 1 1 1, .combine 3 2 1 1] [] [], some [0, 0, 1]⟩] = true := by decide +kernel

-- cut_equals_duplicate_when; independently expected true in Lean
example : checkGoalLemmas ⟨[.var 0, .var 1, .var 2, .var 3], [.lt (.const 0) (.const 0)]⟩ (.split (sp [(0, 1)] 0)
  (.leafAt [((sp [] 1), .fact 0)] [.input 0] [] [])
  (.leafAt [((sp [] 1), .fact 0)] [.input 0] [] [])) [⟨[(sp [(0, 1)] 0), (sp [(0, 1)] 0)], (sp [(0, 1)] 0), .leafAt [((sp [(0, (-1))] 1), .any), ((sp [(0, 1)] 0), .any)] [.input 0, .input 1, .combine 0 1 1 1] [] [], some []⟩] = true := by decide +kernel

-- repeated_split; independently expected true in Lean
example : checkGoalLemmas ⟨[.var 0, .var 1, .var 2, .var 3], [.lt (.const 0) (.const 0)]⟩ (.split (sp [(0, 1)] 0)
  (.split (sp [(0, 1)] 0)
  (.leafAt [((sp [] 1), .fact 0)] [.input 0] [] [])
  (.leafAt [((sp [] 1), .fact 0)] [.input 0] [] []))
  (.split (sp [(0, 1)] 0)
  (.leafAt [((sp [] 1), .fact 0)] [.input 0] [] [])
  (.leafAt [((sp [] 1), .fact 0)] [.input 0] [] []))) [⟨[(sp [] 1)], (sp [] 0), .leafAt [((sp [] 1), .any)] [.input 0] [] [], some []⟩] = true := by decide +kernel

-- constant_split; independently expected true in Lean
example : checkGoalLemmas ⟨[.var 0, .var 1, .var 2, .var 3], [.lt (.const 0) (.const 0)]⟩ (.split (sp [] 0)
  (.leafAt [((sp [] 1), .fact 0)] [.input 0] [] [])
  (.leafAt [((sp [] 1), .fact 0)] [.input 0] [] [])) [⟨[(sp [] 1)], (sp [] 0), .leafAt [((sp [] 1), .any)] [.input 0] [] [], some []⟩] = true := by decide +kernel

-- fresh_unbound_name_is_arbitrary_nat; independently expected true in Lean
example : checkGoalLemmas ⟨[.var 0, .var 1, .var 2, .var 3], [.lt (.const 0) (.const 0)]⟩ (.leafAt [((sp [] 1), .fact 0)] [.input 0] [] []) [⟨[], (sp [(3, (-1))] 0), .leafAt [((sp [(3, 1)] 1), .any), ((sp [(3, (-1))] 0), .nat 3)] [.input 0, .input 1, .combine 0 1 1 1] [] [], some []⟩] = true := by decide +kernel

def zeroRow : Row := ⟨[(3, 0)], 0⟩
def zeroLemma : CutLemma := ⟨[zeroRow], lunit 0, .leaf [lsub (lunit 0) (lunit 1), lunit 1, flip (lunit 0)] [.input 0, .input 1, .input 2, .combine 0 1 1 1, .combine 3 2 1 1] [] [], some [0,1]⟩
def zeroGoal : Goal := ⟨[.var 0,.var 1,.var 2,.var 3], [.le (.var 0) (.var 1), .le (.var 1) (.const 0), .lt (.const 0) (.var 0), .le (.var 2) (.const 0)]⟩
example : lemmaActive [] zeroLemma = true := by decide +kernel
example : checkGoalLemmas zeroGoal (.leaf [lunit 0, flip (lunit 0)] [.input 0,.input 1,.combine 0 1 1 1] [] []) [zeroLemma] = true := by decide +kernel
