import History
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! A sliding-window limit with a history (core/models.ts's windowLimit) through Kern.hmachine_sound: the window ceiling,
with the kernel's trees. -/

-- window limit: window_ceiling: admitted in the window <= c, with sets (carried none; quantified flags none)
--   (variables 0 w, 1 c, 2 now, 3 forced, 4 t, 5 seen, 6 ours, 7 #, 8 ?admitted, 9 r.forced, 10 r.t; maps )
def window_hist : HMachine := ⟨⟨⟨⟨[3, 4, 5],
  [],
  [],
  [],
  [],
  .le (.const 0) (.const 0),
  .or (.eq (.var 3) (.const 0)) (.eq (.var 3) (.const 1))⟩,
  [(8, .and (.eq (.var 3) (.const 0)) (.le (.add (.var 5) (.const 1)) (.var 1)))]⟩,
  [],
  [],
  [],
  [],
  [],
  []⟩,
  .or (.eq (.var 3) (.const 1)) (.eq (.var 8) (.const 1)),
  [3, 4],
  [9, 10],
  [(6, .ite (.and (.eq (.var 9) (.const 0)) (.and (.le (.var 10) (.var 2)) (.lt (.var 2) (.add (.var 10) (.var 0))))) (.const 1) (.const 0))],
  [(5, .ite (.lt (.var 4) (.add (.var 10) (.var 0))) (.const 1) (.const 0))],
  [(.le (.var 4) (.var 2), .var 6, .var 5)]⟩
def window_machine : SMachine := window_hist.plain
def window_l0 : MLaw := ⟨.le (.var 6) (.var 1), none⟩
def window_e0 : SEntry := ⟨window_l0, 7, [], [], [], [], [], [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10], [.not (.le (.const 0) (.var 1))], .leafAt [((sp [(1, 1)] 1), .fact 0), ((sp [(1, (-1))] 0), .nat 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .term (.ite (.and (.eq (.var 3) (.const 0)) (.and (.le (.var 4) (.var 2)) (.lt (.var 2) (.add (.var 4) (.var 0))))) (.const 1) (.const 0)), .term (.ite (.or (.eq (.var 3) (.const 1)) (.and (.eq (.var 3) (.const 0)) (.le (.add (.var 5) (.const 1)) (.var 1)))) (.ite (.and (.eq (.var 3) (.const 0)) (.and (.le (.var 4) (.var 2)) (.lt (.var 2) (.add (.var 4) (.var 0))))) (.const 1) (.const 0)) (.const 0))], [.and (.or (.eq (.var 3) (.const 0)) (.eq (.var 3) (.const 1))) (.and (.or (.not (.le (.var 4) (.var 2))) (.le (.var 6) (.var 5))) (.le (.const 0) (.const 0))), .le (.var 6) (.var 1), .not (.le (.add (.var 6) (.ite (.or (.eq (.var 3) (.const 1)) (.and (.eq (.var 3) (.const 0)) (.le (.add (.var 5) (.const 1)) (.var 1)))) (.ite (.and (.eq (.var 3) (.const 0)) (.and (.le (.var 4) (.var 2)) (.lt (.var 2) (.add (.var 4) (.var 0))))) (.const 1) (.const 0)) (.const 0))) (.var 1))], .split (sp [(3, 1)] (-1))
  (.split (sp [(3, (-1))] 1)
  (.leafAt [((sp [(1, (-1)), (6, 1)] 0), .fact 1), ((sp [(1, 1), (6, (-1))] 1), .fact 2)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.split (sp [(3, (-1))] 0)
  (.split (sp [(1, (-1)), (5, 1)] 1)
  (.split (sp [(2, (-1)), (4, 1)] 0)
  (.split (sp [(0, (-1)), (2, 1), (4, (-1))] 1)
  (.leafAt [((sp [(1, (-1)), (5, 1)] 1), .atom 2), ((sp [(5, (-1)), (6, 1)] 0), .fact 0), ((sp [(1, 1), (6, (-1))] 0), .fact 2)] [.input 0, .input 1, .input 2, .combine 1 2 1 1, .combine 0 3 1 1] [] [])
  (.leafAt [((sp [(1, (-1)), (5, 1)] 1), .atom 2), ((sp [(5, (-1)), (6, 1)] 0), .fact 0), ((sp [(1, 1), (6, (-1))] 1), .fact 2)] [.input 0, .input 1, .input 2, .combine 0 1 1 1, .combine 2 3 1 1] [] []))
  (.leafAt [((sp [(1, (-1)), (6, 1)] 0), .fact 1), ((sp [(1, 1), (6, (-1))] 1), .fact 2)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(1, (-1)), (6, 1)] 0), .fact 1), ((sp [(1, 1), (6, (-1))] 1), .fact 2)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [] 1), .fact 0)] [.input 0] [] [])))
  (.leafAt [((sp [(3, (-1))] 2), .atom 0), ((sp [(3, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def window_proof : List SEntry := [window_e0]
theorem window_check : checkSMachine window_machine window_proof = true := by decide +kernel
theorem window_laws : ∀ ρ M, SReach window_machine ρ M → ∀ e ∈ window_proof, e.Holds ρ M :=
  smachine_sound window_machine window_proof window_check
def window_records : List (List VDef × Tree) := [([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .term (.ite (.and (.eq (.var 9) (.const 0)) (.and (.le (.var 10) (.var 2)) (.lt (.var 2) (.add (.var 10) (.var 0))))) (.const 1) (.const 0)), .term (.ite (.lt (.var 4) (.add (.var 10) (.var 0))) (.const 1) (.const 0))], .split (sp [(9, 1)] 0)
  (.split (sp [(9, (-1))] 0)
  (.split (sp [(2, (-1)), (10, 1)] 0)
  (.split (sp [(0, (-1)), (2, 1), (10, (-1))] 1)
  (.split (sp [(0, (-1)), (4, 1), (10, (-1))] 1)
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])
  (.leafAt [((sp [(0, (-1)), (2, 1), (10, (-1))] 1), .atom 1), ((sp [(0, 1), (4, (-1)), (10, 1)] 0), .atom 0), ((sp [(2, (-1)), (4, 1)] 0), .fact 0)] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 3 1 1 1] [] []))
  (.split (sp [(0, (-1)), (4, 1), (10, (-1))] 1)
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])))
  (.split (sp [(0, (-1)), (4, 1), (10, (-1))] 1)
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])))
  (.leafAt [((sp [(9, 1)] 1), .atom 0), ((sp [(9, (-1))] 0), .nat 9)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split (sp [(0, (-1)), (4, 1), (10, (-1))] 1)
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])))]
theorem window_hcheck : checkHMachine window_hist window_proof window_records = true := by decide +kernel
theorem window_hlaws : ∀ ρ M hist, HReach window_hist ρ M hist → ∀ e ∈ window_proof, e.Holds ρ M :=
  hmachine_sound window_hist window_proof window_records window_hcheck
namespace window
abbrev «c» : Nat := 1
abbrev «ours» : Nat := 6
/-- window_ceiling: admitted in the window <= c -/
theorem law0 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (hist : List (Nat → Nat)) (h : HReach window_hist ρ μ hist) : ρ «ours» ≤ ρ «c» := by
  have hl : window_l0.Holds ρ μ := window_hlaws ρ μ hist h window_e0 (by simp [window_proof])
  exact (evalC_iff ρ μ window_l0.holds).mp hl
end window
-- TAMPERED: the relation claimed at every t (not only t <= now), offered the same proofs. Lean computes the check to false.
def window_tampered0 : HMachine := ⟨⟨⟨⟨[3, 4, 5],
  [],
  [],
  [],
  [],
  .le (.const 0) (.const 0),
  .or (.eq (.var 3) (.const 0)) (.eq (.var 3) (.const 1))⟩,
  [(8, .and (.eq (.var 3) (.const 0)) (.le (.add (.var 5) (.const 1)) (.var 1)))]⟩,
  [],
  [],
  [],
  [],
  [],
  []⟩,
  .or (.eq (.var 3) (.const 1)) (.eq (.var 8) (.const 1)),
  [3, 4],
  [9, 10],
  [(6, .ite (.and (.eq (.var 9) (.const 0)) (.and (.le (.var 10) (.var 2)) (.lt (.var 2) (.add (.var 10) (.var 0))))) (.const 1) (.const 0))],
  [(5, .ite (.lt (.var 4) (.add (.var 10) (.var 0))) (.const 1) (.const 0))],
  [(.eq (.const 0) (.const 0), .var 6, .var 5)]⟩
example : checkHMachine window_tampered0 window_proof window_records = false := by decide +kernel
-- TAMPERED: the relation left out (no record goal), offered the same machine proof. Lean computes the check to false.
def window_tampered1 : HMachine := ⟨⟨⟨⟨[3, 4, 5],
  [],
  [],
  [],
  [],
  .le (.const 0) (.const 0),
  .or (.eq (.var 3) (.const 0)) (.eq (.var 3) (.const 1))⟩,
  [(8, .and (.eq (.var 3) (.const 0)) (.le (.add (.var 5) (.const 1)) (.var 1)))]⟩,
  [],
  [],
  [],
  [],
  [],
  []⟩,
  .or (.eq (.var 3) (.const 1)) (.eq (.var 8) (.const 1)),
  [3, 4],
  [9, 10],
  [(6, .ite (.and (.eq (.var 9) (.const 0)) (.and (.le (.var 10) (.var 2)) (.lt (.var 2) (.add (.var 10) (.var 0))))) (.const 1) (.const 0))],
  [(5, .ite (.lt (.var 4) (.add (.var 10) (.var 0))) (.const 1) (.const 0))],
  []⟩
example : checkHMachine window_tampered1 window_proof [] = false := by decide +kernel

-- The window ceiling in plain Lean: in every reachable state, the admitted requests in the window (variable 6,
-- the sum over the history) are at most c (variable 1), for every history of forced and admitted requests.
theorem window_ceiling (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hist : List (Nat → Nat)) (h : HReach window_hist ρ M hist) :
    ρ 6 ≤ ρ 1 :=
  window.law0 ρ M hist h

#print axioms window_hlaws
#print axioms window_ceiling
