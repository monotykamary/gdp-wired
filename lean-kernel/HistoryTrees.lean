import History
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! A sliding-window limit with a history (core/models.ts's windowLimit) through Kern.hmachine_sound: the window ceiling,
with the kernel's trees. -/

-- window limit: window_ceiling: admitted in the window <= c, with a history (sums ours; queries seen; 1 relation(s))
--   (variables 0 w, 1 c, 2 now, 3 forced, 4 t, 5 seen, 6 ours, 7 #, 8 ?admitted, 9 r.forced, 10 r.t; maps )
def window_machine : HMachine := ⟨⟨⟨[3, 4, 5],
  [],
  [],
  [],
  [],
  .le (.const 0) (.const 0),
  .or (.eq (.var 3) (.const 0)) (.eq (.var 3) (.const 1))⟩,
  [(8, .and (.eq (.var 3) (.const 0)) (.le (.add (.var 5) (.const 1)) (.var 1)))]⟩,
  .or (.eq (.var 3) (.const 1)) (.eq (.var 8) (.const 1)),
  [3, 4],
  [9, 10],
  [(6, .ite (.and (.eq (.var 9) (.const 0)) (.and (.le (.var 10) (.var 2)) (.lt (.var 2) (.add (.var 10) (.var 0))))) (.const 1) (.const 0))],
  [(5, .ite (.lt (.var 4) (.add (.var 10) (.var 0))) (.const 1) (.const 0))],
  [(.le (.var 4) (.var 2), .var 6, .var 5)]⟩
def window_l0 : MLaw := ⟨.le (.var 6) (.var 1), none⟩
def window_e0 : MEntry := ⟨window_l0, 7, [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10], .leaf [⟨[0, 1], 1⟩, ⟨[0, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10], .split ⟨[0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, (-1), 0, 1], 0⟩
  (.split ⟨[0, 0, 0, (-1)], 0⟩
  (.split ⟨[0, (-1), 0, 0, 0, 1], 1⟩
  (.split ⟨[(-1), 0, 1, 0, (-1)], 1⟩
  (.leaf [⟨[0, (-1), 0, 0, 0, 1], 1⟩, ⟨[0, 0, 0, 0, 0, (-1), 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, (-1)], 0⟩] [.input 0, .input 1, .input 2, .combine 1 2 1 1, .combine 0 3 1 1] [] [])
  (.leaf [⟨[0, (-1), 0, 0, 0, 1], 1⟩, ⟨[0, 0, 0, 0, 0, (-1), 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .input 2, .combine 0 1 1 1, .combine 2 3 1 1] [] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[], 1⟩] [.input 0] [] []))
  (.split ⟨[0, 0, 0, (-1)], 0⟩
  (.split ⟨[0, (-1), 0, 0, 0, 1], 1⟩
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[], 1⟩] [.input 0] [] [])))
  (.split ⟨[0, 0, (-1), 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 1], (-1)⟩
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leaf [⟨[], 1⟩] [.input 0] [] []))
  (.split ⟨[0, 0, 0, 1], (-1)⟩
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leaf [⟨[], 1⟩] [.input 0] [] []))))⟩
def window_proof : List MEntry := [window_e0]
def window_records : List (List VDef × Tree) := [([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10], .split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 1, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩
  (.split ⟨[(-1), 0, 0, 0, 1, 0, 0, 0, 0, 0, (-1)], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [] [])
  (.leaf [⟨[(-1), 0, 1, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[1, 0, 0, 0, (-1), 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 3 1 1 1] [] []))
  (.split ⟨[(-1), 0, 0, 0, 1, 0, 0, 0, 0, 0, (-1)], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [] [])
  (.leaf [⟨[], 1⟩] [.input 0] [] [])))
  (.split ⟨[(-1), 0, 0, 0, 1, 0, 0, 0, 0, 0, (-1)], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [] [])
  (.leaf [⟨[], 1⟩] [.input 0] [] [])))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[(-1), 0, 0, 0, 1, 0, 0, 0, 0, 0, (-1)], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [] [])
  (.leaf [⟨[], 1⟩] [.input 0] [] [])))]
theorem window_check : checkHMachine window_machine window_proof window_records = true := by decide +kernel
theorem window_laws : ∀ ρ M hist, HReach window_machine ρ M hist → ∀ e ∈ window_proof, e.law.Holds ρ M :=
  hmachine_sound window_machine window_proof window_records window_check
namespace window
abbrev «c» : Nat := 1
abbrev «ours» : Nat := 6
/-- window_ceiling: admitted in the window <= c -/
theorem law0 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (hist : List (Nat → Nat)) (h : HReach window_machine ρ μ hist) : ρ «ours» ≤ ρ «c» := by
  have hl : window_l0.Holds ρ μ := window_laws ρ μ hist h window_e0 (by simp [window_proof])
  exact (evalC_iff ρ μ window_l0.holds).mp hl
end window
-- The window ceiling in plain Lean: in every reachable state, the admitted requests in the window (variable 6,
-- the sum over the history) are at most c (variable 1), for every history of forced and admitted requests.
theorem window_ceiling (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hist : List (Nat → Nat)) (h : HReach window_machine ρ M hist) :
    ρ 6 ≤ ρ 1 :=
  window.law0 ρ M hist h
-- TAMPERED: the relation claimed at every t (not only t <= now), offered the same proofs. Lean computes the check to false.
def window_tampered0 : HMachine := ⟨⟨⟨[3, 4, 5],
  [],
  [],
  [],
  [],
  .le (.const 0) (.const 0),
  .or (.eq (.var 3) (.const 0)) (.eq (.var 3) (.const 1))⟩,
  [(8, .and (.eq (.var 3) (.const 0)) (.le (.add (.var 5) (.const 1)) (.var 1)))]⟩,
  .or (.eq (.var 3) (.const 1)) (.eq (.var 8) (.const 1)),
  [3, 4],
  [9, 10],
  [(6, .ite (.and (.eq (.var 9) (.const 0)) (.and (.le (.var 10) (.var 2)) (.lt (.var 2) (.add (.var 10) (.var 0))))) (.const 1) (.const 0))],
  [(5, .ite (.lt (.var 4) (.add (.var 10) (.var 0))) (.const 1) (.const 0))],
  [(.eq (.const 0) (.const 0), .var 6, .var 5)]⟩
example : checkHMachine window_tampered0 window_proof window_records = false := by decide +kernel
-- TAMPERED: the relation left out (no record goal), offered the same machine proof. Lean computes the check to false.
def window_tampered1 : HMachine := ⟨⟨⟨[3, 4, 5],
  [],
  [],
  [],
  [],
  .le (.const 0) (.const 0),
  .or (.eq (.var 3) (.const 0)) (.eq (.var 3) (.const 1))⟩,
  [(8, .and (.eq (.var 3) (.const 0)) (.le (.add (.var 5) (.const 1)) (.var 1)))]⟩,
  .or (.eq (.var 3) (.const 1)) (.eq (.var 8) (.const 1)),
  [3, 4],
  [9, 10],
  [(6, .ite (.and (.eq (.var 9) (.const 0)) (.and (.le (.var 10) (.var 2)) (.lt (.var 2) (.add (.var 10) (.var 0))))) (.const 1) (.const 0))],
  [(5, .ite (.lt (.var 4) (.add (.var 10) (.var 0))) (.const 1) (.const 0))],
  []⟩
example : checkHMachine window_tampered1 window_proof [] = false := by decide +kernel

#print axioms window_laws
#print axioms window_ceiling
