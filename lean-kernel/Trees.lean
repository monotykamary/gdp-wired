import Live
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! 7 goals from gdp-wired's kernel (kernel/prove.ts trees), each checked by Lean's kernel against Kern.checkGoal,
whose soundness (Kern.sound) is proven in Kernel.lean. Goals: budget rule; in-flight; products. -/

-- loss: bounded_loss: s <= b + m  (variables 0 b, 1 m, 2 c, 3 s)
def policy_machine : Machine := ⟨[2],
  [(3, .const 0)],
  [(3, .ite (.lt (.var 3) (.var 0)) (.add (.var 3) (.min (.var 2) (.var 1))) (.var 3))],
  .le (.const 0) (.const 0),
  .le (.const 0) (.const 0)⟩
def policy_proof : MachineProof := [(.le (.var 3) (.add (.var 0) (.var 1)),
  ([.var 0, .var 1, .var 2, .var 3], .leafAt [((sp [(0, 1), (1, 1)] 1), .fact 0), ((sp [(0, (-1))] 0), .nat 0), ((sp [(1, (-1))] 0), .nat 1)] [.input 0, .input 1, .input 2, .combine 0 1 1 1, .combine 3 2 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .term (.min (.var 2) (.var 1)), .term (.ite (.lt (.var 3) (.var 0)) (.add (.var 3) (.min (.var 2) (.var 1))) (.var 3))], .split (sp [(0, (-1)), (3, 1)] 1)
  (.split (sp [(1, (-1)), (2, 1)] 0)
  (.leafAt [((sp [(0, (-1)), (3, 1)] 1), .atom 1), ((sp [(1, (-1)), (2, 1)] 0), .atom 0), ((sp [(0, 1), (1, 1), (2, (-1)), (3, (-1))] 1), .fact 1)] [.input 0, .input 1, .input 2, .combine 2 0 1 1, .combine 1 3 1 1] [] [])
  (.leafAt [((sp [(0, (-1)), (3, 1)] 1), .atom 1), ((sp [(0, 1), (3, (-1))] 1), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(0, (-1)), (1, (-1)), (3, 1)] 0), .fact 0), ((sp [(0, 1), (1, 1), (3, (-1))] 1), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))]
theorem policy_laws : ∀ maps ρ, Reach policy_machine maps ρ → ∀ l ∈ policy_proof.map (·.1), evalC ρ maps l = true :=
  machine_sound policy_machine policy_proof (by decide +kernel)
-- the budget rule's law in plain Lean: in every reachable state, s <= b + m (b, m, c, s are variables 0..3).
theorem bounded_loss (maps : Nat → Nat → Nat) (ρ : Nat → Nat) (h : Reach policy_machine maps ρ) : ρ 3 ≤ ρ 0 + ρ 1 := by
  have := policy_laws maps ρ h _ (List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩)
  simp only [evalC, evalE] at this
  exact of_decide_eq_true this

-- in-flight requests: in-flight loss: s <= b + 3 × 50; s + 50p <= b + 150  (variables 0 b, 1 t, 2 done, 3 s, 4 p)
def inflight_machine : Machine := ⟨[1, 2],
  [(3, .const 0), (4, .const 0)],
  [(3, .ite (.and (.eq (.var 2) (.const 1)) (.lt (.const 0) (.var 4))) (.add (.var 3) (.min (.var 1) (.const 50))) (.var 3)), (4, .ite (.eq (.var 2) (.const 1)) (.ite (.lt (.const 0) (.var 4)) (.sub (.var 4) (.const 1)) (.var 4)) (.ite (.and (.lt (.var 3) (.var 0)) (.lt (.var 4) (.const 3))) (.add (.var 4) (.const 1)) (.var 4)))],
  .le (.const 0) (.const 0),
  .or (.eq (.var 2) (.const 0)) (.eq (.var 2) (.const 1))⟩
def inflight_proof : MachineProof := [(.le (.var 3) (.add (.var 0) (.const 150)),
  ([.var 0, .var 1, .var 2, .var 3, .var 4], .leafAt [((sp [(0, 1)] 151), .fact 0), ((sp [(0, (-1))] 0), .nat 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .term (.min (.var 1) (.const 50)), .term (.ite (.and (.eq (.var 2) (.const 1)) (.lt (.const 0) (.var 4))) (.add (.var 3) (.min (.var 1) (.const 50))) (.var 3))], .split (sp [(2, 1)] (-1))
  (.split (sp [(2, (-1))] 1)
  (.split (sp [(4, (-1))] 1)
  (.split (sp [(1, 1)] (-50))
  (.leafAt [((sp [(4, (-1))] 1), .atom 1), ((sp [(1, 1)] (-50)), .atom 0), ((sp [(0, (-1)), (3, 1), (4, 50)] (-150)), .fact 2), ((sp [(0, 1), (1, (-1)), (3, (-1))] 151), .fact 3)] [.input 0, .input 1, .input 2, .input 3, .combine 2 0 1 50, .combine 1 3 1 1, .combine 4 5 1 1] [] [])
  (.leafAt [((sp [(4, (-1))] 1), .atom 1), ((sp [(0, (-1)), (3, 1), (4, 50)] (-150)), .fact 2), ((sp [(0, 1), (3, (-1))] 101), .fact 3)] [.input 0, .input 1, .input 2, .combine 1 0 1 50, .combine 3 2 1 1] [] []))
  (.leafAt [((sp [(0, (-1)), (3, 1)] (-150)), .fact 1), ((sp [(0, 1), (3, (-1))] 151), .fact 3)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(0, (-1)), (3, 1)] (-150)), .fact 1), ((sp [(0, 1), (3, (-1))] 151), .fact 3)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(2, (-1))] 2), .atom 0), ((sp [(2, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []))), (.le (.add (.var 3) (.mul 50 (.var 4))) (.add (.var 0) (.const 150)),
  ([.var 0, .var 1, .var 2, .var 3, .var 4], .leafAt [((sp [(0, 1)] 151), .fact 0), ((sp [(0, (-1))] 0), .nat 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .term (.min (.var 1) (.const 50)), .term (.ite (.and (.eq (.var 2) (.const 1)) (.lt (.const 0) (.var 4))) (.add (.var 3) (.min (.var 1) (.const 50))) (.var 3)), .term (.ite (.and (.lt (.var 3) (.var 0)) (.lt (.var 4) (.const 3))) (.add (.var 4) (.const 1)) (.var 4)), .term (.sub (.var 4) (.const 1)), .term (.ite (.lt (.const 0) (.var 4)) (.sub (.var 4) (.const 1)) (.var 4)), .term (.ite (.eq (.var 2) (.const 1)) (.ite (.lt (.const 0) (.var 4)) (.sub (.var 4) (.const 1)) (.var 4)) (.ite (.and (.lt (.var 3) (.var 0)) (.lt (.var 4) (.const 3))) (.add (.var 4) (.const 1)) (.var 4)))], .split (sp [(2, 1)] (-1))
  (.split (sp [(2, (-1))] 1)
  (.split (sp [(4, (-1))] 1)
  (.split (sp [(1, 1)] (-50))
  (.leafAt [((sp [(1, 1)] (-50)), .atom 0), ((sp [(0, (-1)), (3, 1), (4, 50)] (-150)), .fact 2), ((sp [(0, 1), (1, (-1)), (3, (-1)), (4, (-50))] 201), .fact 3)] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 3 1 1 1] [] [])
  (.leafAt [((sp [(0, (-1)), (3, 1), (4, 50)] (-150)), .fact 2), ((sp [(0, 1), (3, (-1)), (4, (-50))] 151), .fact 3)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(4, 1)] 0), .atom 0), ((sp [(0, (-1)), (3, 1)] (-150)), .fact 1), ((sp [(0, 1), (3, (-1)), (4, (-50))] 151), .fact 3)] [.input 0, .input 1, .input 2, .combine 2 0 1 50, .combine 3 1 1 1] [] []))
  (.split (sp [(0, (-1)), (3, 1)] 1)
  (.split (sp [(4, 1)] (-2))
  (.leafAt [((sp [(0, (-1)), (3, 1)] 1), .atom 1), ((sp [(4, 1)] (-2)), .atom 0), ((sp [(0, 1), (3, (-1)), (4, (-50))] 101), .fact 3)] [.input 0, .input 1, .input 2, .combine 2 0 1 1, .cut 3 50 [(4, (-1))] 3, .combine 1 4 1 1] [] [])
  (.leafAt [((sp [(0, (-1)), (3, 1), (4, 50)] (-150)), .fact 2), ((sp [(0, 1), (3, (-1)), (4, (-50))] 151), .fact 3)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(0, (-1)), (3, 1), (4, 50)] (-150)), .fact 2), ((sp [(0, 1), (3, (-1)), (4, (-50))] 151), .fact 3)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))
  (.leafAt [((sp [(2, (-1))] 2), .atom 0), ((sp [(2, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))]
theorem inflight_laws : ∀ maps ρ, Reach inflight_machine maps ρ → ∀ l ∈ inflight_proof.map (·.1), evalC ρ maps l = true :=
  machine_sound inflight_machine inflight_proof (by decide +kernel)
-- the in-flight law in plain Lean: s <= b + 150 (b, t, done, s, p are variables 0..4).
theorem inflight_loss (maps : Nat → Nat → Nat) (ρ : Nat → Nat) (h : Reach inflight_machine maps ρ) : ρ 3 ≤ ρ 0 + 150 := by
  have := inflight_laws maps ρ h _ (List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩)
  simp only [evalC, evalE] at this
  exact of_decide_eq_true this

-- loss, counted: s <= m × requests  (variables 0 m, 1 c, 2 s, 3 r)
def counted_machine : Machine := ⟨[1],
  [(2, .const 0), (3, .const 0)],
  [(2, .add (.var 2) (.min (.var 1) (.var 0))), (3, .add (.var 3) (.const 1))],
  .le (.const 0) (.const 0),
  .le (.const 0) (.const 0)⟩
def counted_proof : MachineProof := [(.le (.var 2) (.prod (.var 0) (.var 3)),
  ([.var 0, .var 1, .var 2, .var 3], .leafAt [((sp [] 1), .fact 0)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .mono [0, 3], .term (.min (.var 1) (.var 0))], .split (sp [(0, (-1)), (1, 1)] 0)
  (.leafAt [((sp [(0, (-1)), (1, 1)] 0), .atom 0), ((sp [(2, 1), (4, (-1))] 0), .fact 0), ((sp [(0, 1), (1, (-1)), (2, (-1)), (4, 1)] 1), .fact 1)] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 1 3 1 1] [] [])
  (.leafAt [((sp [(2, 1), (4, (-1))] 0), .fact 0), ((sp [(2, (-1)), (4, 1)] 1), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))]
theorem counted_laws : ∀ maps ρ, Reach counted_machine maps ρ → ∀ l ∈ counted_proof.map (·.1), evalC ρ maps l = true :=
  machine_sound counted_machine counted_proof (by decide +kernel)
-- In plain Lean: after any requests, s <= m · r (m, c, s, r are variables 0..3).
theorem loss_per_request (maps : Nat → Nat → Nat) (ρ : Nat → Nat) (h : Reach counted_machine maps ρ) : ρ 2 ≤ ρ 0 * ρ 3 := by
  have := counted_laws maps ρ h _ (List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩)
  simp only [evalC, evalE] at this
  exact of_decide_eq_true this

-- TAMPERED: the budget rule's proof offered for the machine with the max_tokens cap forgotten. Lean computes the check to false.
def uncapped_machine : Machine := ⟨[2], [(3, .const 0)], [(3, .ite (.lt (.var 3) (.var 0)) (.add (.var 3) (.var 2)) (.var 3))], .le (.const 0) (.const 0), .le (.const 0) (.const 0)⟩
example : checkMachine uncapped_machine policy_proof = false := by decide +kernel

-- gcd by subtraction: a >= 1; b >= 1, with sets (carried none; quantified flags none)
--   (variables 0 A, 1 B, 2 a, 3 b, 4 #, 5 a', 6 b'; maps )
def gcd_loop : Loop := ⟨[],
  [(2, .var 0), (3, .var 1)],
  [(2, .ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)), (3, .ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3))],
  .not (.eq (.var 2) (.var 3)),
  .and (.le (.const 1) (.var 0)) (.le (.const 1) (.var 1)),
  .le (.const 0) (.const 0)⟩
def gcd_machine : SMachine := gcd_loop.machine
def gcd_l0 : MLaw := ⟨.le (.const 1) (.var 2), none⟩
def gcd_e0 : SEntry := ⟨gcd_l0, 4, [], [], [], [], [], [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6], [.and (.le (.const 1) (.var 0)) (.le (.const 1) (.var 1)), .not (.le (.const 1) (.var 0))], .leafAt [((sp [(0, (-1))] 1), .fact 0), ((sp [(0, 1)] 0), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .term (.sub (.var 2) (.var 3)), .term (.ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)), .term (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)) (.var 2))], [.and (.le (.const 1) (.var 0)) (.le (.const 1) (.var 1)), .le (.const 1) (.var 2), .le (.const 1) (.var 3), .not (.le (.const 1) (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)) (.var 2)))], .split (sp [(2, 1), (3, (-1))] 0)
  (.split (sp [(2, (-1)), (3, 1)] 0)
  (.leafAt [((sp [(2, 1), (3, (-1))] 0), .atom 1), ((sp [(2, (-1)), (3, 1)] 0), .atom 0), ((sp [(2, (-1))] 1), .fact 1), ((sp [(2, 1)] 0), .fact 3)] [.input 0, .input 1, .input 2, .input 3, .combine 2 0 1 1, .combine 3 1 1 1, .combine 4 5 1 1] [] [])
  (.leafAt [((sp [(2, (-1))] 1), .fact 1), ((sp [(2, 1)] 0), .fact 3)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split (sp [(2, (-1)), (3, 1)] 0)
  (.leafAt [((sp [] 1), .fact 3)] [.input 0] [] [])
  (.leafAt [((sp [(2, (-1)), (3, 1)] 1), .atom 1), ((sp [(2, 1), (3, (-1))] 1), .atom 0)] [.input 0, .input 1, .combine 1 0 1 1] [] [])))⟩
def gcd_l1 : MLaw := ⟨.le (.const 1) (.var 3), none⟩
def gcd_e1 : SEntry := ⟨gcd_l1, 4, [], [], [], [], [], [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6], [.and (.le (.const 1) (.var 0)) (.le (.const 1) (.var 1)), .not (.le (.const 1) (.var 1))], .leafAt [((sp [(1, (-1))] 1), .fact 0), ((sp [(1, 1)] 0), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .term (.sub (.var 3) (.var 2)), .term (.ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3)), .term (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3)) (.var 3))], [.and (.le (.const 1) (.var 0)) (.le (.const 1) (.var 1)), .le (.const 1) (.var 2), .le (.const 1) (.var 3), .not (.le (.const 1) (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3)) (.var 3)))], .split (sp [(2, 1), (3, (-1))] 0)
  (.split (sp [(2, (-1)), (3, 1)] 0)
  (.leafAt [((sp [(2, 1), (3, (-1))] 0), .atom 1), ((sp [(2, (-1))] 1), .fact 1), ((sp [(3, 1)] 0), .fact 3)] [.input 0, .input 1, .input 2, .combine 1 0 1 1, .combine 3 2 1 1] [] [])
  (.leafAt [((sp [] 1), .fact 3)] [.input 0] [] []))
  (.split (sp [(2, 1), (3, (-1))] 1)
  (.leafAt [((sp [(2, (-1)), (3, 1)] 1), .atom 1), ((sp [(2, 1), (3, (-1))] 1), .atom 0)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(3, (-1))] 1), .fact 2), ((sp [(3, 1)] 0), .fact 3)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩
def gcd_proof : List SEntry := [gcd_e0, gcd_e1]
theorem gcd_check : checkSMachine gcd_machine gcd_proof = true := by decide +kernel
theorem gcd_laws : ∀ ρ M, SReach gcd_machine ρ M → ∀ e ∈ gcd_proof, e.Holds ρ M :=
  smachine_sound gcd_machine gcd_proof gcd_check
namespace gcd
abbrev «a» : Nat := 2
abbrev «b» : Nat := 3
/-- a >= 1 -/
theorem law0 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : SReach gcd_machine ρ μ) : 1 ≤ ρ «a» := by
  have hl : gcd_l0.Holds ρ μ := gcd_laws ρ μ h gcd_e0 (by simp [gcd_proof])
  exact (evalC_iff ρ μ gcd_l0.holds).mp hl
/-- b >= 1 -/
theorem law1 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : SReach gcd_machine ρ μ) : 1 ≤ ρ «b» := by
  have hl : gcd_l1.Holds ρ μ := gcd_laws ρ μ h gcd_e1 (by simp [gcd_proof])
  exact (evalC_iff ρ μ gcd_l1.holds).mp hl
end gcd

-- Liveness: gcd by subtraction halts
def gcd_live0 : Live := ⟨.le (.const 0) (.const 0), .not (.not (.eq (.var 2) (.var 3))), [.add (.var 2) (.var 3)],
  [(.le (.const 0) (.const 0), [])],
  [(2, 5), (3, 6)],
  []⟩
def gcd_live0_sp : SProof := ([], [], [], [], [], ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .term (.sub (.var 2) (.var 3)), .term (.ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)), .term (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)) (.var 2)), .term (.sub (.var 3) (.var 2)), .term (.ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3)), .term (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3)) (.var 3))], [.and (.le (.const 1) (.var 0)) (.le (.const 1) (.var 1)), .le (.const 1) (.var 2), .le (.const 1) (.var 3), .and (.le (.const 0) (.const 0)) (.not (.not (.not (.eq (.var 2) (.var 3))))), .not (.and (.or (.le (.const 0) (.const 0)) (.not (.not (.eq (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)) (.var 2)) (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3)) (.var 3)))))) (.or (.not (.not (.eq (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)) (.var 2)) (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3)) (.var 3))))) (.or (.or (.lt (.add (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)) (.var 2)) (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3)) (.var 3))) (.add (.var 2) (.var 3))) (.and (.eq (.add (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)) (.var 2)) (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3)) (.var 3))) (.add (.var 2) (.var 3))) (.lt (.const 0) (.const 0)))) (.and (.and (.eq (.add (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)) (.var 2)) (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3)) (.var 3))) (.add (.var 2) (.var 3))) (.le (.const 0) (.const 0))) (.and (.or (.not (.le (.const 0) (.const 0))) (.le (.const 0) (.const 0))) (.le (.const 0) (.const 0)))))))], .split (sp [(2, 1), (3, (-1))] 0)
  (.split (sp [(2, (-1)), (3, 1)] 0)
  (.leafAt [((sp [] 1), .fact 3)] [.input 0] [] [])
  (.leafAt [((sp [(2, (-1))] 1), .fact 1), ((sp [(2, 1)] 0), .fact 4)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split (sp [(2, (-1)), (3, 1)] 0)
  (.leafAt [((sp [(3, (-1))] 1), .fact 2), ((sp [(3, 1)] 0), .fact 4)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leafAt [((sp [] 1), .fact 4)] [.input 0] [] []))))
def gcd_live0_cp : SProof := ([], [], [], [], [], ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6], [.and (.le (.const 1) (.var 0)) (.le (.const 1) (.var 1)), .le (.const 1) (.var 2), .le (.const 1) (.var 3), .and (.le (.const 0) (.const 0)) (.not (.not (.not (.eq (.var 2) (.var 3))))), .not (.or (.le (.const 0) (.const 0)) (.lt (.const 0) (.const 0)))], .leafAt [((sp [] 1), .fact 4)] [.input 0] [] []))
def gcd_live0_hp : List SProof := [([], [], [], [], [], ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .term (.sub (.var 2) (.var 3)), .term (.ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)), .term (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)) (.var 2)), .term (.sub (.var 3) (.var 2)), .term (.ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3)), .term (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3)) (.var 3))], [.and (.le (.const 1) (.var 0)) (.le (.const 1) (.var 1)), .le (.const 1) (.var 2), .le (.const 1) (.var 3), .and (.and (.le (.const 0) (.const 0)) (.not (.not (.not (.eq (.var 2) (.var 3)))))) (.and (.le (.const 0) (.const 0)) (.le (.const 0) (.const 0))), .not (.or (.not (.not (.eq (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)) (.var 2)) (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3)) (.var 3))))) (.or (.lt (.add (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)) (.var 2)) (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3)) (.var 3))) (.add (.var 2) (.var 3))) (.and (.eq (.add (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)) (.var 2)) (.ite (.not (.eq (.var 2) (.var 3))) (.ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3)) (.var 3))) (.add (.var 2) (.var 3))) (.lt (.const 0) (.const 0)))))], .split (sp [(2, 1), (3, (-1))] 0)
  (.split (sp [(2, (-1)), (3, 1)] 0)
  (.leafAt [((sp [] 1), .fact 3)] [.input 0] [] [])
  (.leafAt [((sp [(2, (-1))] 1), .fact 1), ((sp [(2, 1)] 0), .fact 4)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split (sp [(2, (-1)), (3, 1)] 0)
  (.leafAt [((sp [(3, (-1))] 1), .fact 2), ((sp [(3, 1)] 0), .fact 4)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leafAt [((sp [] 1), .fact 4)] [.input 0] [] []))))]
theorem gcd_live0_ok : sliveOk gcd_machine gcd_live0 = true := by decide +kernel
theorem gcd_live0_stay : checkSKStep gcd_machine gcd_proof (sliveStep gcd_live0 gcd_live0.pend (liveStayC gcd_live0) gcd_live0_sp) = true := by decide +kernel
theorem gcd_live0_cover : checkSKStep gcd_machine gcd_proof (sliveStep gcd_live0 gcd_live0.pend (liveCoverC gcd_live0) gcd_live0_cp) = true := by decide +kernel
theorem gcd_live0_helps : sliveHelpsOk gcd_machine gcd_proof gcd_live0 gcd_live0_hp = true := by decide +kernel
/-- gcd by subtraction halts: along every run that takes each helpful request infinitely often, `from` is followed by `to`. -/
theorem gcd_live0_holds (run : SRun gcd_machine)
    (fair : ∀ h ∈ gcd_live0.helps, ∀ n, ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 gcd_live0.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 gcd_live0.to = true :=
  sleads_sound gcd_machine gcd_proof gcd_live0 _ _ _ gcd_check gcd_live0_ok gcd_live0_stay gcd_live0_cover gcd_live0_helps run fair
def gcd_live0_ap : List (List (Nat × E) × SProof × List E) := [([], ([], [], [], [], [], ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6], [.and (.le (.const 1) (.var 0)) (.le (.const 1) (.var 1)), .le (.const 1) (.var 2), .le (.const 1) (.var 3), .and (.and (.and (.le (.const 0) (.const 0)) (.not (.not (.not (.eq (.var 2) (.var 3)))))) (.and (.le (.const 0) (.const 0)) (.le (.const 0) (.const 0)))) (.le (.const 0) (.const 0)), .not (.le (.const 0) (.const 0))], .leafAt [((sp [] 1), .fact 4)] [.input 0] [] [])), [])]
theorem gcd_live0_allows : sliveAllowsOk gcd_machine gcd_proof gcd_live0 gcd_live0_ap = true := by decide +kernel
/-- gcd by subtraction halts, under weak fairness: along every run that takes each helpful request whenever, from some point on, it
stays allowed, `from` is followed by `to`. -/
theorem gcd_live0_holds_wf (run : SRun gcd_machine)
    (fair : ∀ h ∈ gcd_live0.helps, ∀ n, (∀ m, n ≤ m → ∃ ι κ, (∀ p ∈ h.2, ι p.1 = evalE (run.st m).1 (run.st m).2 p.2)
        ∧ evalC (sView gcd_machine (run.st m).1 (run.st m).2 ι κ).1 (sView gcd_machine (run.st m).1 (run.st m).2 ι κ).2 gcd_machine.f.m.assume = true) →
      ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 gcd_live0.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 gcd_live0.to = true :=
  sleads_wf_sound gcd_machine gcd_proof gcd_live0 _ _ _ _ gcd_check gcd_live0_ok gcd_live0_stay gcd_live0_cover gcd_live0_helps gcd_live0_allows run fair

/-- gcd by subtraction halts: for params meeting its precondition, no run of turns goes on forever. -/
theorem gcd_halts : ∀ maps ρ0, evalC ρ0 maps gcd_loop.pre = true →
    ¬ ∃ f : Nat → Nat → Nat, f 0 = applyS gcd_loop.init ρ0 maps ∧ ∀ n, Turn gcd_loop maps (f n) (f (n + 1)) :=
  loop_halts_of gcd_loop gcd_live0 rfl rfl (by intro h hh; simp only [gcd_live0, List.mem_singleton] at hh; subst hh; rfl) (by decide +kernel) gcd_live0_holds
-- TAMPERED: the gcd proof without the precondition A, B >= 1. Lean computes the checks to false.
def gcd_tampered : SMachine := Loop.machine ⟨[],
  [(2, .var 0), (3, .var 1)],
  [(2, .ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)), (3, .ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3))],
  .not (.eq (.var 2) (.var 3)),
  .le (.const 0) (.const 0),
  .le (.const 0) (.const 0)⟩
example : (checkSMachine gcd_tampered gcd_proof && sliveOk gcd_tampered gcd_live0
    && checkSKStep gcd_tampered gcd_proof (sliveStep gcd_live0 gcd_live0.pend (liveStayC gcd_live0) gcd_live0_sp)
    && checkSKStep gcd_tampered gcd_proof (sliveStep gcd_live0 gcd_live0.pend (liveCoverC gcd_live0) gcd_live0_cp)
    && sliveHelpsOk gcd_tampered gcd_proof gcd_live0 gcd_live0_hp) = false := by decide +kernel

-- pagination: , with sets (carried none; quantified flags none)
--   (variables 0 total, 1 page, 2 cur, 3 #, 4 cur'; maps )
def pages_loop : Loop := ⟨[1],
  [(2, .const 0)],
  [(2, .add (.var 2) (.min (.var 1) (.sub (.var 0) (.var 2))))],
  .lt (.var 2) (.var 0),
  .le (.const 0) (.const 0),
  .le (.const 1) (.var 1)⟩
def pages_machine : SMachine := pages_loop.machine

def pages_proof : List SEntry := []
theorem pages_check : checkSMachine pages_machine pages_proof = true := by decide +kernel
theorem pages_laws : ∀ ρ M, SReach pages_machine ρ M → ∀ e ∈ pages_proof, e.Holds ρ M :=
  smachine_sound pages_machine pages_proof pages_check
namespace pages


end pages

-- Liveness: pagination halts
def pages_live0 : Live := ⟨.le (.const 0) (.const 0), .not (.lt (.var 2) (.var 0)), [.sub (.var 0) (.var 2)],
  [(.le (.const 0) (.const 0), [])],
  [(2, 4)],
  []⟩
def pages_live0_sp : SProof := ([], [], [], [], [], ([.var 0, .var 1, .var 2, .var 3, .var 4, .term (.sub (.var 0) (.var 2)), .term (.min (.var 1) (.sub (.var 0) (.var 2))), .term (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.min (.var 1) (.sub (.var 0) (.var 2)))) (.var 2)), .term (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.min (.var 1) (.sub (.var 0) (.var 2)))) (.var 2)))], [.le (.const 1) (.var 1), .and (.le (.const 0) (.const 0)) (.not (.not (.lt (.var 2) (.var 0)))), .not (.and (.or (.le (.const 0) (.const 0)) (.not (.lt (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.min (.var 1) (.sub (.var 0) (.var 2)))) (.var 2)) (.var 0)))) (.or (.not (.lt (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.min (.var 1) (.sub (.var 0) (.var 2)))) (.var 2)) (.var 0))) (.or (.or (.lt (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.min (.var 1) (.sub (.var 0) (.var 2)))) (.var 2))) (.sub (.var 0) (.var 2))) (.and (.eq (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.min (.var 1) (.sub (.var 0) (.var 2)))) (.var 2))) (.sub (.var 0) (.var 2))) (.lt (.const 0) (.const 0)))) (.and (.and (.eq (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.min (.var 1) (.sub (.var 0) (.var 2)))) (.var 2))) (.sub (.var 0) (.var 2))) (.le (.const 0) (.const 0))) (.and (.or (.not (.le (.const 0) (.const 0))) (.le (.const 0) (.const 0))) (.le (.const 0) (.const 0)))))))], .split (sp [(0, (-1)), (2, 1)] 1)
  (.split (sp [(0, (-1)), (2, 1)] 0)
  (.split (sp [(0, (-1)), (1, 1), (2, 1)] 0)
  (.leafAt [((sp [(1, (-1))] 1), .fact 0), ((sp [(1, 1)] 0), .fact 2)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leafAt [((sp [] 1), .fact 2)] [.input 0] [] []))
  (.leafAt [((sp [(0, (-1)), (2, 1)] 1), .atom 1), ((sp [(0, 1), (2, (-1))] 1), .atom 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [] 1), .fact 2)] [.input 0] [] [])))
def pages_live0_cp : SProof := ([], [], [], [], [], ([.var 0, .var 1, .var 2, .var 3, .var 4], [.le (.const 1) (.var 1), .and (.le (.const 0) (.const 0)) (.not (.not (.lt (.var 2) (.var 0)))), .not (.or (.le (.const 0) (.const 0)) (.lt (.const 0) (.const 0)))], .leafAt [((sp [] 1), .fact 2)] [.input 0] [] []))
def pages_live0_hp : List SProof := [([], [], [], [], [], ([.var 0, .var 1, .var 2, .var 3, .var 4, .term (.sub (.var 0) (.var 2)), .term (.min (.var 1) (.sub (.var 0) (.var 2))), .term (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.min (.var 1) (.sub (.var 0) (.var 2)))) (.var 2)), .term (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.min (.var 1) (.sub (.var 0) (.var 2)))) (.var 2)))], [.le (.const 1) (.var 1), .and (.and (.le (.const 0) (.const 0)) (.not (.not (.lt (.var 2) (.var 0))))) (.and (.le (.const 0) (.const 0)) (.le (.const 0) (.const 0))), .not (.or (.not (.lt (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.min (.var 1) (.sub (.var 0) (.var 2)))) (.var 2)) (.var 0))) (.or (.lt (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.min (.var 1) (.sub (.var 0) (.var 2)))) (.var 2))) (.sub (.var 0) (.var 2))) (.and (.eq (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.min (.var 1) (.sub (.var 0) (.var 2)))) (.var 2))) (.sub (.var 0) (.var 2))) (.lt (.const 0) (.const 0)))))], .split (sp [(0, (-1)), (2, 1)] 1)
  (.split (sp [(0, (-1)), (2, 1)] 0)
  (.split (sp [(0, (-1)), (1, 1), (2, 1)] 0)
  (.leafAt [((sp [(1, (-1))] 1), .fact 0), ((sp [(1, 1)] 0), .fact 2)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leafAt [((sp [] 1), .fact 2)] [.input 0] [] []))
  (.leafAt [((sp [(0, (-1)), (2, 1)] 1), .atom 1), ((sp [(0, 1), (2, (-1))] 1), .atom 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(0, 1), (2, (-1))] 0), .atom 0), ((sp [(0, (-1)), (2, 1)] 1), .fact 1)] [.input 0, .input 1, .combine 1 0 1 1] [] [])))]
theorem pages_live0_ok : sliveOk pages_machine pages_live0 = true := by decide +kernel
theorem pages_live0_stay : checkSKStep pages_machine pages_proof (sliveStep pages_live0 pages_live0.pend (liveStayC pages_live0) pages_live0_sp) = true := by decide +kernel
theorem pages_live0_cover : checkSKStep pages_machine pages_proof (sliveStep pages_live0 pages_live0.pend (liveCoverC pages_live0) pages_live0_cp) = true := by decide +kernel
theorem pages_live0_helps : sliveHelpsOk pages_machine pages_proof pages_live0 pages_live0_hp = true := by decide +kernel
/-- pagination halts: along every run that takes each helpful request infinitely often, `from` is followed by `to`. -/
theorem pages_live0_holds (run : SRun pages_machine)
    (fair : ∀ h ∈ pages_live0.helps, ∀ n, ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 pages_live0.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 pages_live0.to = true :=
  sleads_sound pages_machine pages_proof pages_live0 _ _ _ pages_check pages_live0_ok pages_live0_stay pages_live0_cover pages_live0_helps run fair
def pages_live0_ap : List (List (Nat × E) × SProof × List E) := [([(1, .var 0)], ([], [], [], [], [], ([.var 0, .var 1, .var 2, .var 3, .var 4], [.le (.const 0) (.const 0), .and (.and (.and (.le (.const 0) (.const 0)) (.not (.not (.lt (.var 2) (.var 0))))) (.and (.le (.const 0) (.const 0)) (.le (.const 0) (.const 0)))) (.and (.eq (.var 1) (.var 0)) (.le (.const 0) (.const 0))), .not (.le (.const 1) (.var 1))], .leafAt [((sp [(0, (-1)), (2, 1)] 1), .fact 1), ((sp [(0, 1), (1, (-1))] 0), .fact 1), ((sp [(1, 1)] 0), .fact 2), ((sp [(2, (-1))] 0), .nat 2)] [.input 0, .input 1, .input 2, .input 3, .combine 2 1 1 1, .combine 0 4 1 1, .combine 5 3 1 1] [] [])), [])]
theorem pages_live0_allows : sliveAllowsOk pages_machine pages_proof pages_live0 pages_live0_ap = true := by decide +kernel
/-- pagination halts, under weak fairness: along every run that takes each helpful request whenever, from some point on, it
stays allowed, `from` is followed by `to`. -/
theorem pages_live0_holds_wf (run : SRun pages_machine)
    (fair : ∀ h ∈ pages_live0.helps, ∀ n, (∀ m, n ≤ m → ∃ ι κ, (∀ p ∈ h.2, ι p.1 = evalE (run.st m).1 (run.st m).2 p.2)
        ∧ evalC (sView pages_machine (run.st m).1 (run.st m).2 ι κ).1 (sView pages_machine (run.st m).1 (run.st m).2 ι κ).2 pages_machine.f.m.assume = true) →
      ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 pages_live0.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 pages_live0.to = true :=
  sleads_wf_sound pages_machine pages_proof pages_live0 _ _ _ _ pages_check pages_live0_ok pages_live0_stay pages_live0_cover pages_live0_helps pages_live0_allows run fair

/-- pagination halts: for params meeting its precondition, no run of turns goes on forever. -/
theorem pages_halts : ∀ maps ρ0, evalC ρ0 maps pages_loop.pre = true →
    ¬ ∃ f : Nat → Nat → Nat, f 0 = applyS pages_loop.init ρ0 maps ∧ ∀ n, Turn pages_loop maps (f n) (f (n + 1)) :=
  loop_halts_of pages_loop pages_live0 rfl rfl (by intro h hh; simp only [pages_live0, List.mem_singleton] at hh; subst hh; rfl) (by decide +kernel) pages_live0_holds
-- TAMPERED: the pagination proof when a page may be empty. Lean computes the checks to false.
def pages_tampered : SMachine := Loop.machine ⟨[1],
  [(2, .const 0)],
  [(2, .add (.var 2) (.min (.var 1) (.sub (.var 0) (.var 2))))],
  .lt (.var 2) (.var 0),
  .le (.const 0) (.const 0),
  .le (.const 0) (.var 1)⟩
example : (checkSMachine pages_tampered pages_proof && sliveOk pages_tampered pages_live0
    && checkSKStep pages_tampered pages_proof (sliveStep pages_live0 pages_live0.pend (liveStayC pages_live0) pages_live0_sp)
    && checkSKStep pages_tampered pages_proof (sliveStep pages_live0 pages_live0.pend (liveCoverC pages_live0) pages_live0_cp)
    && sliveHelpsOk pages_tampered pages_proof pages_live0 pages_live0_hp) = false := by decide +kernel

-- retry: , with sets (carried none; quantified flags none)
--   (variables 0 budget, 1 wait, 2 spent, 3 tries, 4 #, 5 spent', 6 tries'; maps )
def retry_loop : Loop := ⟨[1],
  [(2, .const 0), (3, .const 0)],
  [(2, .add (.var 2) (.max (.const 1) (.var 1))), (3, .add (.var 3) (.const 1))],
  .lt (.var 2) (.var 0),
  .le (.const 0) (.const 0),
  .le (.const 0) (.const 0)⟩
def retry_machine : SMachine := retry_loop.machine

def retry_proof : List SEntry := []
theorem retry_check : checkSMachine retry_machine retry_proof = true := by decide +kernel
theorem retry_laws : ∀ ρ M, SReach retry_machine ρ M → ∀ e ∈ retry_proof, e.Holds ρ M :=
  smachine_sound retry_machine retry_proof retry_check
namespace retry


end retry

-- Liveness: retry halts
def retry_live0 : Live := ⟨.le (.const 0) (.const 0), .not (.lt (.var 2) (.var 0)), [.sub (.var 0) (.var 2)],
  [(.le (.const 0) (.const 0), [])],
  [(2, 5), (3, 6)],
  []⟩
def retry_live0_sp : SProof := ([], [], [], [], [], ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .term (.max (.const 1) (.var 1)), .term (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.max (.const 1) (.var 1))) (.var 2)), .term (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.max (.const 1) (.var 1))) (.var 2))), .term (.sub (.var 0) (.var 2))], [.and (.le (.const 0) (.const 0)) (.not (.not (.lt (.var 2) (.var 0)))), .not (.and (.or (.le (.const 0) (.const 0)) (.not (.lt (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.max (.const 1) (.var 1))) (.var 2)) (.var 0)))) (.or (.not (.lt (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.max (.const 1) (.var 1))) (.var 2)) (.var 0))) (.or (.or (.lt (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.max (.const 1) (.var 1))) (.var 2))) (.sub (.var 0) (.var 2))) (.and (.eq (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.max (.const 1) (.var 1))) (.var 2))) (.sub (.var 0) (.var 2))) (.lt (.const 0) (.const 0)))) (.and (.and (.eq (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.max (.const 1) (.var 1))) (.var 2))) (.sub (.var 0) (.var 2))) (.le (.const 0) (.const 0))) (.and (.or (.not (.le (.const 0) (.const 0))) (.le (.const 0) (.const 0))) (.le (.const 0) (.const 0)))))))], .split (sp [(0, (-1)), (2, 1)] 1)
  (.split (sp [(1, (-1))] 1)
  (.split (sp [(0, (-1)), (1, 1), (2, 1)] 0)
  (.split (sp [(0, (-1)), (2, 1)] 0)
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])
  (.leafAt [((sp [(0, (-1)), (2, 1)] 1), .atom 3), ((sp [(0, 1), (2, (-1))] 1), .atom 0)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(0, 1), (1, (-1)), (2, (-1))] 1), .atom 0), ((sp [(0, (-1)), (1, 1), (2, 1)] 1), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split (sp [(0, (-1)), (2, 1)] 0)
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])
  (.leafAt [((sp [(0, 1), (2, (-1))] 1), .atom 0), ((sp [(0, (-1)), (2, 1)] 2), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])))
def retry_live0_cp : SProof := ([], [], [], [], [], ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6], [.and (.le (.const 0) (.const 0)) (.not (.not (.lt (.var 2) (.var 0)))), .not (.or (.le (.const 0) (.const 0)) (.lt (.const 0) (.const 0)))], .leafAt [((sp [] 1), .fact 1)] [.input 0] [] []))
def retry_live0_hp : List SProof := [([], [], [], [], [], ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .term (.max (.const 1) (.var 1)), .term (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.max (.const 1) (.var 1))) (.var 2)), .term (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.max (.const 1) (.var 1))) (.var 2))), .term (.sub (.var 0) (.var 2))], [.and (.and (.le (.const 0) (.const 0)) (.not (.not (.lt (.var 2) (.var 0))))) (.and (.le (.const 0) (.const 0)) (.le (.const 0) (.const 0))), .not (.or (.not (.lt (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.max (.const 1) (.var 1))) (.var 2)) (.var 0))) (.or (.lt (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.max (.const 1) (.var 1))) (.var 2))) (.sub (.var 0) (.var 2))) (.and (.eq (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.add (.var 2) (.max (.const 1) (.var 1))) (.var 2))) (.sub (.var 0) (.var 2))) (.lt (.const 0) (.const 0)))))], .split (sp [(0, (-1)), (2, 1)] 1)
  (.split (sp [(1, (-1))] 1)
  (.split (sp [(0, (-1)), (1, 1), (2, 1)] 0)
  (.split (sp [(0, (-1)), (2, 1)] 0)
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])
  (.leafAt [((sp [(0, (-1)), (2, 1)] 1), .atom 3), ((sp [(0, 1), (2, (-1))] 1), .atom 0)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(0, 1), (1, (-1)), (2, (-1))] 1), .atom 0), ((sp [(0, (-1)), (1, 1), (2, 1)] 1), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split (sp [(0, (-1)), (2, 1)] 0)
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])
  (.leafAt [((sp [(0, 1), (2, (-1))] 1), .atom 0), ((sp [(0, (-1)), (2, 1)] 2), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))
  (.leafAt [((sp [(0, 1), (2, (-1))] 0), .atom 0), ((sp [(0, (-1)), (2, 1)] 1), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))]
theorem retry_live0_ok : sliveOk retry_machine retry_live0 = true := by decide +kernel
theorem retry_live0_stay : checkSKStep retry_machine retry_proof (sliveStep retry_live0 retry_live0.pend (liveStayC retry_live0) retry_live0_sp) = true := by decide +kernel
theorem retry_live0_cover : checkSKStep retry_machine retry_proof (sliveStep retry_live0 retry_live0.pend (liveCoverC retry_live0) retry_live0_cp) = true := by decide +kernel
theorem retry_live0_helps : sliveHelpsOk retry_machine retry_proof retry_live0 retry_live0_hp = true := by decide +kernel
/-- retry halts: along every run that takes each helpful request infinitely often, `from` is followed by `to`. -/
theorem retry_live0_holds (run : SRun retry_machine)
    (fair : ∀ h ∈ retry_live0.helps, ∀ n, ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 retry_live0.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 retry_live0.to = true :=
  sleads_sound retry_machine retry_proof retry_live0 _ _ _ retry_check retry_live0_ok retry_live0_stay retry_live0_cover retry_live0_helps run fair
def retry_live0_ap : List (List (Nat × E) × SProof × List E) := [([], ([], [], [], [], [], ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6], [.le (.const 0) (.const 0), .and (.and (.and (.le (.const 0) (.const 0)) (.not (.not (.lt (.var 2) (.var 0))))) (.and (.le (.const 0) (.const 0)) (.le (.const 0) (.const 0)))) (.le (.const 0) (.const 0)), .not (.le (.const 0) (.const 0))], .leafAt [((sp [] 1), .fact 2)] [.input 0] [] [])), [])]
theorem retry_live0_allows : sliveAllowsOk retry_machine retry_proof retry_live0 retry_live0_ap = true := by decide +kernel
/-- retry halts, under weak fairness: along every run that takes each helpful request whenever, from some point on, it
stays allowed, `from` is followed by `to`. -/
theorem retry_live0_holds_wf (run : SRun retry_machine)
    (fair : ∀ h ∈ retry_live0.helps, ∀ n, (∀ m, n ≤ m → ∃ ι κ, (∀ p ∈ h.2, ι p.1 = evalE (run.st m).1 (run.st m).2 p.2)
        ∧ evalC (sView retry_machine (run.st m).1 (run.st m).2 ι κ).1 (sView retry_machine (run.st m).1 (run.st m).2 ι κ).2 retry_machine.f.m.assume = true) →
      ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 retry_live0.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 retry_live0.to = true :=
  sleads_wf_sound retry_machine retry_proof retry_live0 _ _ _ _ retry_check retry_live0_ok retry_live0_stay retry_live0_cover retry_live0_helps retry_live0_allows run fair

/-- retry halts: for params meeting its precondition, no run of turns goes on forever. -/
theorem retry_halts : ∀ maps ρ0, evalC ρ0 maps retry_loop.pre = true →
    ¬ ∃ f : Nat → Nat → Nat, f 0 = applyS retry_loop.init ρ0 maps ∧ ∀ n, Turn retry_loop maps (f n) (f (n + 1)) :=
  loop_halts_of retry_loop retry_live0 rfl rfl (by intro h hh; simp only [retry_live0, List.mem_singleton] at hh; subst hh; rfl) (by decide +kernel) retry_live0_holds

-- every cell of an n × m grid: , with sets (carried none; quantified flags none)
--   (variables 0 n, 1 m, 2 i, 3 j, 4 #, 5 i', 6 j'; maps )
def grid_loop : Loop := ⟨[],
  [(2, .const 0), (3, .const 0)],
  [(2, .ite (.lt (.var 3) (.var 1)) (.var 2) (.add (.var 2) (.const 1))), (3, .ite (.lt (.var 3) (.var 1)) (.add (.var 3) (.const 1)) (.const 0))],
  .lt (.var 2) (.var 0),
  .le (.const 0) (.const 0),
  .le (.const 0) (.const 0)⟩
def grid_machine : SMachine := grid_loop.machine

def grid_proof : List SEntry := []
theorem grid_check : checkSMachine grid_machine grid_proof = true := by decide +kernel
theorem grid_laws : ∀ ρ M, SReach grid_machine ρ M → ∀ e ∈ grid_proof, e.Holds ρ M :=
  smachine_sound grid_machine grid_proof grid_check
namespace grid


end grid

-- Liveness: every cell of an n × m grid halts
def grid_live0 : Live := ⟨.le (.const 0) (.const 0), .not (.lt (.var 2) (.var 0)), [.sub (.var 0) (.var 2), .sub (.var 1) (.var 3)],
  [(.le (.const 0) (.const 0), [])],
  [(2, 5), (3, 6)],
  []⟩
def grid_live0_sp : SProof := ([], [], [], [], [], ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .term (.ite (.lt (.var 3) (.var 1)) (.var 2) (.add (.var 2) (.const 1))), .term (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.var 2) (.add (.var 2) (.const 1))) (.var 2)), .term (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.var 2) (.add (.var 2) (.const 1))) (.var 2))), .term (.sub (.var 0) (.var 2)), .term (.ite (.lt (.var 3) (.var 1)) (.add (.var 3) (.const 1)) (.const 0)), .term (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.add (.var 3) (.const 1)) (.const 0)) (.var 3)), .term (.sub (.var 1) (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.add (.var 3) (.const 1)) (.const 0)) (.var 3))), .term (.sub (.var 1) (.var 3))], [.and (.le (.const 0) (.const 0)) (.not (.not (.lt (.var 2) (.var 0)))), .not (.and (.or (.le (.const 0) (.const 0)) (.not (.lt (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.var 2) (.add (.var 2) (.const 1))) (.var 2)) (.var 0)))) (.or (.not (.lt (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.var 2) (.add (.var 2) (.const 1))) (.var 2)) (.var 0))) (.or (.or (.lt (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.var 2) (.add (.var 2) (.const 1))) (.var 2))) (.sub (.var 0) (.var 2))) (.and (.eq (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.var 2) (.add (.var 2) (.const 1))) (.var 2))) (.sub (.var 0) (.var 2))) (.or (.lt (.sub (.var 1) (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.add (.var 3) (.const 1)) (.const 0)) (.var 3))) (.sub (.var 1) (.var 3))) (.and (.eq (.sub (.var 1) (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.add (.var 3) (.const 1)) (.const 0)) (.var 3))) (.sub (.var 1) (.var 3))) (.lt (.const 0) (.const 0)))))) (.and (.and (.eq (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.var 2) (.add (.var 2) (.const 1))) (.var 2))) (.sub (.var 0) (.var 2))) (.and (.eq (.sub (.var 1) (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.add (.var 3) (.const 1)) (.const 0)) (.var 3))) (.sub (.var 1) (.var 3))) (.le (.const 0) (.const 0)))) (.and (.or (.not (.le (.const 0) (.const 0))) (.le (.const 0) (.const 0))) (.le (.const 0) (.const 0)))))))], .split (sp [(0, (-1)), (2, 1)] 1)
  (.split (sp [(1, (-1)), (3, 1)] 1)
  (.split (sp [(0, (-1)), (2, 1)] 0)
  (.split (sp [(1, (-1)), (3, 1)] 0)
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])
  (.leafAt [((sp [(1, 1), (3, (-1))] 1), .atom 0), ((sp [(1, (-1)), (3, 1)] 2), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(0, (-1)), (2, 1)] 1), .atom 2), ((sp [(0, 1), (2, (-1))] 1), .atom 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split (sp [(0, (-1)), (2, 1)] 0)
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])
  (.leafAt [((sp [(0, 1), (2, (-1))] 1), .atom 0), ((sp [(0, (-1)), (2, 1)] 2), .fact 1)] [.input 0, .input 1, .combine 1 0 1 1] [] [])))
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])))
def grid_live0_cp : SProof := ([], [], [], [], [], ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6], [.and (.le (.const 0) (.const 0)) (.not (.not (.lt (.var 2) (.var 0)))), .not (.or (.le (.const 0) (.const 0)) (.lt (.const 0) (.const 0)))], .leafAt [((sp [] 1), .fact 1)] [.input 0] [] []))
def grid_live0_hp : List SProof := [([], [], [], [], [], ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .term (.ite (.lt (.var 3) (.var 1)) (.var 2) (.add (.var 2) (.const 1))), .term (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.var 2) (.add (.var 2) (.const 1))) (.var 2)), .term (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.var 2) (.add (.var 2) (.const 1))) (.var 2))), .term (.sub (.var 0) (.var 2)), .term (.ite (.lt (.var 3) (.var 1)) (.add (.var 3) (.const 1)) (.const 0)), .term (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.add (.var 3) (.const 1)) (.const 0)) (.var 3)), .term (.sub (.var 1) (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.add (.var 3) (.const 1)) (.const 0)) (.var 3))), .term (.sub (.var 1) (.var 3))], [.and (.and (.le (.const 0) (.const 0)) (.not (.not (.lt (.var 2) (.var 0))))) (.and (.le (.const 0) (.const 0)) (.le (.const 0) (.const 0))), .not (.or (.not (.lt (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.var 2) (.add (.var 2) (.const 1))) (.var 2)) (.var 0))) (.or (.lt (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.var 2) (.add (.var 2) (.const 1))) (.var 2))) (.sub (.var 0) (.var 2))) (.and (.eq (.sub (.var 0) (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.var 2) (.add (.var 2) (.const 1))) (.var 2))) (.sub (.var 0) (.var 2))) (.or (.lt (.sub (.var 1) (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.add (.var 3) (.const 1)) (.const 0)) (.var 3))) (.sub (.var 1) (.var 3))) (.and (.eq (.sub (.var 1) (.ite (.lt (.var 2) (.var 0)) (.ite (.lt (.var 3) (.var 1)) (.add (.var 3) (.const 1)) (.const 0)) (.var 3))) (.sub (.var 1) (.var 3))) (.lt (.const 0) (.const 0)))))))], .split (sp [(0, (-1)), (2, 1)] 1)
  (.split (sp [(1, (-1)), (3, 1)] 1)
  (.split (sp [(0, (-1)), (2, 1)] 0)
  (.split (sp [(1, (-1)), (3, 1)] 0)
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])
  (.leafAt [((sp [(1, (-1)), (3, 1)] 1), .atom 2), ((sp [(1, 1), (3, (-1))] 1), .atom 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(0, (-1)), (2, 1)] 1), .atom 2), ((sp [(0, 1), (2, (-1))] 1), .atom 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split (sp [(0, (-1)), (2, 1)] 0)
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])
  (.leafAt [((sp [(0, 1), (2, (-1))] 1), .atom 0), ((sp [(0, (-1)), (2, 1)] 2), .fact 1)] [.input 0, .input 1, .combine 1 0 1 1] [] [])))
  (.leafAt [((sp [(0, 1), (2, (-1))] 0), .atom 0), ((sp [(0, (-1)), (2, 1)] 1), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))]
theorem grid_live0_ok : sliveOk grid_machine grid_live0 = true := by decide +kernel
theorem grid_live0_stay : checkSKStep grid_machine grid_proof (sliveStep grid_live0 grid_live0.pend (liveStayC grid_live0) grid_live0_sp) = true := by decide +kernel
theorem grid_live0_cover : checkSKStep grid_machine grid_proof (sliveStep grid_live0 grid_live0.pend (liveCoverC grid_live0) grid_live0_cp) = true := by decide +kernel
theorem grid_live0_helps : sliveHelpsOk grid_machine grid_proof grid_live0 grid_live0_hp = true := by decide +kernel
/-- every cell of an n × m grid halts: along every run that takes each helpful request infinitely often, `from` is followed by `to`. -/
theorem grid_live0_holds (run : SRun grid_machine)
    (fair : ∀ h ∈ grid_live0.helps, ∀ n, ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 grid_live0.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 grid_live0.to = true :=
  sleads_sound grid_machine grid_proof grid_live0 _ _ _ grid_check grid_live0_ok grid_live0_stay grid_live0_cover grid_live0_helps run fair
def grid_live0_ap : List (List (Nat × E) × SProof × List E) := [([], ([], [], [], [], [], ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6], [.le (.const 0) (.const 0), .and (.and (.and (.le (.const 0) (.const 0)) (.not (.not (.lt (.var 2) (.var 0))))) (.and (.le (.const 0) (.const 0)) (.le (.const 0) (.const 0)))) (.le (.const 0) (.const 0)), .not (.le (.const 0) (.const 0))], .leafAt [((sp [] 1), .fact 2)] [.input 0] [] [])), [])]
theorem grid_live0_allows : sliveAllowsOk grid_machine grid_proof grid_live0 grid_live0_ap = true := by decide +kernel
/-- every cell of an n × m grid halts, under weak fairness: along every run that takes each helpful request whenever, from some point on, it
stays allowed, `from` is followed by `to`. -/
theorem grid_live0_holds_wf (run : SRun grid_machine)
    (fair : ∀ h ∈ grid_live0.helps, ∀ n, (∀ m, n ≤ m → ∃ ι κ, (∀ p ∈ h.2, ι p.1 = evalE (run.st m).1 (run.st m).2 p.2)
        ∧ evalC (sView grid_machine (run.st m).1 (run.st m).2 ι κ).1 (sView grid_machine (run.st m).1 (run.st m).2 ι κ).2 grid_machine.f.m.assume = true) →
      ∃ m, n ≤ m ∧ ∀ p ∈ h.2, (run.req m).1 p.1 = evalE (run.st m).1 (run.st m).2 p.2) :
    ∀ n, evalC (run.st n).1 (run.st n).2 grid_live0.from_ = true → ∃ m, n ≤ m ∧ evalC (run.st m).1 (run.st m).2 grid_live0.to = true :=
  sleads_wf_sound grid_machine grid_proof grid_live0 _ _ _ _ grid_check grid_live0_ok grid_live0_stay grid_live0_cover grid_live0_helps grid_live0_allows run fair

/-- every cell of an n × m grid halts: for params meeting its precondition, no run of turns goes on forever. -/
theorem grid_halts : ∀ maps ρ0, evalC ρ0 maps grid_loop.pre = true →
    ¬ ∃ f : Nat → Nat → Nat, f 0 = applyS grid_loop.init ρ0 maps ∧ ∀ n, Turn grid_loop maps (f n) (f (n + 1)) :=
  loop_halts_of grid_loop grid_live0 rfl rfl (by intro h hh; simp only [grid_live0, List.mem_singleton] at hh; subst hh; rfl) (by decide +kernel) grid_live0_holds

-- TAMPERED: while x < w, x := x + 1, with the rank w ∸ x (w the turn's input): the rank drops each turn, yet the loop
-- runs forever when every turn sends w = x + 1. Its halting, stated as a liveness, reads the input w in `to` and the rank;
-- Lean's check refuses it (kernel.ts refuses both).
def forever_loop : Loop := ⟨[0], [(1, .const 0)], [(1, .add (.var 1) (.const 1))], .lt (.var 1) (.var 0), .le (.const 0) (.const 0), .le (.const 0) (.const 0)⟩
def forever_live : Live := ⟨.le (.const 0) (.const 0), .not (.lt (.var 1) (.var 0)), [.sub (.var 0) (.var 1)], [(.le (.const 0) (.const 0), [])], [(1, 2)], []⟩
example : sliveOk forever_loop.machine forever_live = false := by decide +kernel

-- shape: leaves = nodes + 1; height <= nodes; height < leaves  (variables 0 leaves, 1 nodes, 2 height, 3 l_leaves, 4 l_nodes, 5 l_height, 6 r_leaves, 7 r_nodes, 8 r_height)
def shape_fold : Fold := ⟨[],
  [(0, 3, 6), (1, 4, 7), (2, 5, 8)],
  [(0, .const 1), (1, .const 0), (2, .const 0)],
  [(0, .add (.var 3) (.var 6)), (1, .add (.add (.var 4) (.var 7)) (.const 1)), (2, .add (.max (.var 5) (.var 8)) (.const 1))],
  .le (.const 0) (.const 0),
  .le (.const 0) (.const 0)⟩
def shape_proof : FoldProof := [(.eq (.var 0) (.add (.var 1) (.const 1)),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8], .leafAt [((sp [] 1), .fact 0)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8], .split (sp [(3, 1), (4, (-1)), (6, 1), (7, (-1))] (-2))
  (.leafAt [((sp [(3, (-1)), (4, 1)] 1), .fact 0), ((sp [(6, (-1)), (7, 1)] 1), .fact 1), ((sp [(3, 1), (4, (-1)), (6, 1), (7, (-1))] (-1)), .fact 6)] [.input 0, .input 1, .input 2, .combine 2 0 1 1, .combine 3 1 1 1] [] [])
  (.leafAt [((sp [(3, (-1)), (4, 1), (6, (-1)), (7, 1)] 3), .atom 0), ((sp [(3, 1), (4, (-1))] (-1)), .fact 0), ((sp [(6, 1), (7, (-1))] (-1)), .fact 1)] [.input 0, .input 1, .input 2, .combine 0 1 1 1, .combine 3 2 1 1] [] []))), (.le (.var 2) (.var 1),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8], .leafAt [((sp [] 1), .fact 0)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .term (.max (.var 5) (.var 8))], .split (sp [(5, 1), (8, (-1))] 0)
  (.leafAt [((sp [(7, (-1)), (8, 1)] 0), .fact 3), ((sp [(4, 1), (7, 1), (8, (-1))] 1), .fact 6), ((sp [(4, (-1))] 0), .nat 4)] [.input 0, .input 1, .input 2, .combine 0 1 1 1, .combine 3 2 1 1] [] [])
  (.leafAt [((sp [(4, (-1)), (5, 1)] 0), .fact 2), ((sp [(4, 1), (5, (-1)), (7, 1)] 1), .fact 6), ((sp [(7, (-1))] 0), .nat 7)] [.input 0, .input 1, .input 2, .combine 0 1 1 1, .combine 3 2 1 1] [] []))), (.lt (.var 2) (.var 0),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8], .leafAt [((sp [] 1), .fact 0)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .term (.max (.var 5) (.var 8))], .split (sp [(5, 1), (8, (-1))] 0)
  (.leafAt [((sp [(3, (-1)), (4, 1)] 1), .fact 0), ((sp [(6, (-1)), (7, 1)] 1), .fact 1), ((sp [(7, (-1)), (8, 1)] 0), .fact 3), ((sp [(3, 1), (6, 1), (8, (-1))] (-1)), .fact 6), ((sp [(4, (-1))] 0), .nat 4)] [.input 0, .input 1, .input 2, .input 3, .input 4, .combine 3 0 1 1, .combine 5 1 1 1, .combine 2 6 1 1, .combine 7 4 1 1] [] [])
  (.leafAt [((sp [(3, (-1)), (4, 1)] 1), .fact 0), ((sp [(6, (-1)), (7, 1)] 1), .fact 1), ((sp [(4, (-1)), (5, 1)] 0), .fact 2), ((sp [(3, 1), (5, (-1)), (6, 1)] (-1)), .fact 6), ((sp [(7, (-1))] 0), .nat 7)] [.input 0, .input 1, .input 2, .input 3, .input 4, .combine 3 0 1 1, .combine 5 1 1 1, .combine 2 6 1 1, .combine 7 4 1 1] [] [])))]
theorem shape_laws : ∀ maps ρ, evalC ρ maps shape_fold.pre = true → ∀ t, Allowed shape_fold ρ maps t →
    ∀ l ∈ shape_proof.map (·.1), evalC (foldT shape_fold ρ maps t) maps l = true :=
  fold_sound shape_fold shape_proof (by decide +kernel)
-- In plain Lean: every binary tree has one more leaf than it has nodes (leaves, nodes, height are variables 0..2).
theorem leaves_eq_nodes_succ (maps : Nat → Nat → Nat) (ρ : Nat → Nat) (t : BTree) :
    foldT shape_fold ρ maps t 0 = foldT shape_fold ρ maps t 1 + 1 := by
  have := shape_laws maps ρ rfl t (allowed_trivial _ rfl ρ maps t) _ (List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩)
  simp only [evalC, evalE] at this
  exact of_decide_eq_true this

-- spend roll-up: spend <= 50 count  (variables 0 c, 1 spend, 2 count, 3 l_spend, 4 l_count, 5 r_spend, 6 r_count)
def rollup_fold : Fold := ⟨[0],
  [(1, 3, 5), (2, 4, 6)],
  [(1, .min (.var 0) (.const 50)), (2, .const 1)],
  [(1, .add (.var 3) (.var 5)), (2, .add (.var 4) (.var 6))],
  .le (.const 0) (.const 0),
  .le (.const 0) (.const 0)⟩
def rollup_proof : FoldProof := [(.le (.var 1) (.mul 50 (.var 2)),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .term (.min (.var 0) (.const 50))], .split (sp [(0, 1)] (-50))
  (.leafAt [((sp [] 1), .fact 0)] [.input 0] [] [])
  (.leafAt [((sp [] 1), .fact 0)] [.input 0] [] [])),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6], .leafAt [((sp [(3, 1), (4, (-50))] 0), .fact 0), ((sp [(5, 1), (6, (-50))] 0), .fact 1), ((sp [(3, (-1)), (4, 50), (5, (-1)), (6, 50)] 1), .fact 2)] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 1 3 1 1] [] []))]
theorem rollup_laws : ∀ maps ρ, evalC ρ maps rollup_fold.pre = true → ∀ t, Allowed rollup_fold ρ maps t →
    ∀ l ∈ rollup_proof.map (·.1), evalC (foldT rollup_fold ρ maps t) maps l = true :=
  fold_sound rollup_fold rollup_proof (by decide +kernel)
-- TAMPERED: the same proof offered for leaves capped at 51. Lean computes the check to false.
def rollup51_fold : Fold := { rollup_fold with leaf := [(1, .min (.var 0) (.const 51)), (2, .const 1)] }
example : checkFold rollup51_fold rollup_proof = false := by decide +kernel

-- admit: once_per_account: every Acct count <= its cap; day_cap: every Day count <= its cap; hour_cap: every Hour count <= its cap; dom_cap: every Dom count <= its cap  (variables 0 d, 1 hr, 2 dm, 3 acct, 4 day, 5 hour, 6 dom, 7 ok, 8 k, 9 k#, 10 #; maps 0 Acct, 1 Day, 2 Hour, 3 Dom)
def admit_machine : FMMachine := ⟨⟨[3, 4, 5, 6, 7],
  [],
  [(0, 0), (1, 0), (2, 0), (3, 0)],
  [],
  [(0, .var 3, .ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3))), (1, .var 4, .ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 1 (.var 4)) (.const 1)) (.get 1 (.var 4))), (2, .var 5, .ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 2 (.var 5)) (.const 1)) (.get 2 (.var 5))), (3, .var 6, .ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 3 (.var 6)) (.const 1)) (.get 3 (.var 6)))],
  .le (.const 0) (.const 0),
  .or (.eq (.var 7) (.const 0)) (.eq (.var 7) (.const 1))⟩,
  []⟩
def admit_l0 : MLaw := ⟨.le (.get 0 (.var 8)) (.const 1), some 8⟩
def admit_e0 : MEntry := ⟨admit_l0, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10], .leafAt [((sp [] 1), .fact 0)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .term (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3))), .term (.ite (.eq (.var 9) (.var 3)) (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3))) (.get 0 (.var 9))), .cell 0 (sp [(3, 1)] 0), .cell 1 (sp [(4, 1)] 0), .cell 2 (sp [(5, 1)] 0), .cell 3 (sp [(6, 1)] 0), .cell 0 (sp [(4, 1)] 0), .cell 0 (sp [(5, 1)] 0), .cell 0 (sp [(6, 1)] 0), .cell 0 (sp [(9, 1)] 0), .cell 1 (sp [(3, 1)] 0), .cell 1 (sp [(5, 1)] 0), .cell 1 (sp [(6, 1)] 0), .cell 1 (sp [(9, 1)] 0), .cell 2 (sp [(3, 1)] 0), .cell 2 (sp [(4, 1)] 0), .cell 2 (sp [(6, 1)] 0), .cell 2 (sp [(9, 1)] 0), .cell 3 (sp [(3, 1)] 0), .cell 3 (sp [(4, 1)] 0), .cell 3 (sp [(5, 1)] 0), .cell 3 (sp [(9, 1)] 0)], .split (sp [(3, (-1)), (9, 1)] 0)
  (.split (sp [(3, 1), (9, (-1))] 0)
  (.split (sp [(7, 1)] (-1))
  (.split (sp [(7, (-1))] 1)
  (.split (sp [(13, 1)] 0)
  (.split (sp [(0, (-1)), (14, 1)] 1)
  (.split (sp [(1, (-1)), (15, 1)] 1)
  (.split (sp [(2, (-1)), (16, 1)] 1)
  (.leafAt [((sp [] 1), .fact 21)] [.input 0] [(13, 20), (21, 24), (25, 28), (29, 32)] [])
  (.leafAt [((sp [(13, 1)] 0), .atom 3), ((sp [(13, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(13, 20), (21, 24), (25, 28), (29, 32)] []))
  (.leafAt [((sp [(13, 1)] 0), .atom 2), ((sp [(13, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(13, 20), (21, 24), (25, 28), (29, 32)] []))
  (.leafAt [((sp [(13, 1)] 0), .atom 1), ((sp [(13, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(13, 20), (21, 24), (25, 28), (29, 32)] []))
  (.leafAt [((sp [(13, 1)] (-1)), .fact 1), ((sp [(13, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(13, 20), (21, 24), (25, 28), (29, 32)] []))
  (.leafAt [((sp [(13, 1)] (-1)), .fact 1), ((sp [(13, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(13, 20), (21, 24), (25, 28), (29, 32)] []))
  (.leafAt [((sp [(7, (-1))] 2), .atom 0), ((sp [(7, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(13, 20), (21, 24), (25, 28), (29, 32)] []))
  (.leafAt [((sp [(20, 1)] (-1)), .fact 5), ((sp [(20, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(20, 1)] (-1)), .fact 5), ((sp [(20, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def admit_l1 : MLaw := ⟨.le (.get 1 (.var 8)) (.var 0), some 8⟩
def admit_e1 : MEntry := ⟨admit_l1, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10], .leafAt [((sp [(0, 1)] 1), .fact 0), ((sp [(0, (-1))] 0), .nat 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .term (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 1 (.var 4)) (.const 1)) (.get 1 (.var 4))), .term (.ite (.eq (.var 9) (.var 4)) (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 1 (.var 4)) (.const 1)) (.get 1 (.var 4))) (.get 1 (.var 9))), .cell 0 (sp [(3, 1)] 0), .cell 1 (sp [(4, 1)] 0), .cell 2 (sp [(5, 1)] 0), .cell 3 (sp [(6, 1)] 0), .cell 0 (sp [(4, 1)] 0), .cell 0 (sp [(5, 1)] 0), .cell 0 (sp [(6, 1)] 0), .cell 0 (sp [(9, 1)] 0), .cell 1 (sp [(3, 1)] 0), .cell 1 (sp [(5, 1)] 0), .cell 1 (sp [(6, 1)] 0), .cell 1 (sp [(9, 1)] 0), .cell 2 (sp [(3, 1)] 0), .cell 2 (sp [(4, 1)] 0), .cell 2 (sp [(6, 1)] 0), .cell 2 (sp [(9, 1)] 0), .cell 3 (sp [(3, 1)] 0), .cell 3 (sp [(4, 1)] 0), .cell 3 (sp [(5, 1)] 0), .cell 3 (sp [(9, 1)] 0)], .split (sp [(4, (-1)), (9, 1)] 0)
  (.split (sp [(4, 1), (9, (-1))] 0)
  (.split (sp [(7, 1)] (-1))
  (.split (sp [(7, (-1))] 1)
  (.split (sp [(13, 1)] 0)
  (.split (sp [(0, (-1)), (14, 1)] 1)
  (.split (sp [(1, (-1)), (15, 1)] 1)
  (.split (sp [(2, (-1)), (16, 1)] 1)
  (.leafAt [((sp [] 1), .fact 21)] [.input 0] [(14, 24), (17, 20), (26, 28), (30, 32)] [])
  (.leafAt [((sp [(0, (-1)), (14, 1)] 1), .atom 2), ((sp [(0, 1), (14, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(14, 24), (17, 20), (26, 28), (30, 32)] []))
  (.leafAt [((sp [(0, (-1)), (14, 1)] 1), .atom 1), ((sp [(0, 1), (14, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(14, 24), (17, 20), (26, 28), (30, 32)] []))
  (.leafAt [((sp [(0, (-1)), (14, 1)] 0), .fact 7), ((sp [(0, 1), (14, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(14, 24), (17, 20), (26, 28), (30, 32)] []))
  (.leafAt [((sp [(0, (-1)), (14, 1)] 0), .fact 7), ((sp [(0, 1), (14, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(14, 24), (17, 20), (26, 28), (30, 32)] []))
  (.leafAt [((sp [(0, (-1)), (14, 1)] 0), .fact 7), ((sp [(0, 1), (14, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(14, 24), (17, 20), (26, 28), (30, 32)] []))
  (.leafAt [((sp [(7, (-1))] 2), .atom 0), ((sp [(7, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(14, 24), (17, 20), (26, 28), (30, 32)] []))
  (.leafAt [((sp [(0, (-1)), (24, 1)] 0), .fact 10), ((sp [(0, 1), (24, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(0, (-1)), (24, 1)] 0), .fact 10), ((sp [(0, 1), (24, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def admit_l2 : MLaw := ⟨.le (.get 2 (.var 8)) (.var 1), some 8⟩
def admit_e2 : MEntry := ⟨admit_l2, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10], .leafAt [((sp [(1, 1)] 1), .fact 0), ((sp [(1, (-1))] 0), .nat 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .term (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 2 (.var 5)) (.const 1)) (.get 2 (.var 5))), .term (.ite (.eq (.var 9) (.var 5)) (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 2 (.var 5)) (.const 1)) (.get 2 (.var 5))) (.get 2 (.var 9))), .cell 0 (sp [(3, 1)] 0), .cell 1 (sp [(4, 1)] 0), .cell 2 (sp [(5, 1)] 0), .cell 3 (sp [(6, 1)] 0), .cell 0 (sp [(4, 1)] 0), .cell 0 (sp [(5, 1)] 0), .cell 0 (sp [(6, 1)] 0), .cell 0 (sp [(9, 1)] 0), .cell 1 (sp [(3, 1)] 0), .cell 1 (sp [(5, 1)] 0), .cell 1 (sp [(6, 1)] 0), .cell 1 (sp [(9, 1)] 0), .cell 2 (sp [(3, 1)] 0), .cell 2 (sp [(4, 1)] 0), .cell 2 (sp [(6, 1)] 0), .cell 2 (sp [(9, 1)] 0), .cell 3 (sp [(3, 1)] 0), .cell 3 (sp [(4, 1)] 0), .cell 3 (sp [(5, 1)] 0), .cell 3 (sp [(9, 1)] 0)], .split (sp [(5, (-1)), (9, 1)] 0)
  (.split (sp [(5, 1), (9, (-1))] 0)
  (.split (sp [(7, 1)] (-1))
  (.split (sp [(7, (-1))] 1)
  (.split (sp [(13, 1)] 0)
  (.split (sp [(0, (-1)), (14, 1)] 1)
  (.split (sp [(1, (-1)), (15, 1)] 1)
  (.split (sp [(2, (-1)), (16, 1)] 1)
  (.leafAt [((sp [] 1), .fact 21)] [.input 0] [(15, 28), (18, 20), (22, 24), (31, 32)] [])
  (.leafAt [((sp [(1, (-1)), (15, 1)] 1), .atom 1), ((sp [(1, 1), (15, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(15, 28), (18, 20), (22, 24), (31, 32)] []))
  (.leafAt [((sp [(1, (-1)), (15, 1)] 0), .fact 13), ((sp [(1, 1), (15, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(15, 28), (18, 20), (22, 24), (31, 32)] []))
  (.leafAt [((sp [(1, (-1)), (15, 1)] 0), .fact 13), ((sp [(1, 1), (15, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(15, 28), (18, 20), (22, 24), (31, 32)] []))
  (.leafAt [((sp [(1, (-1)), (15, 1)] 0), .fact 13), ((sp [(1, 1), (15, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(15, 28), (18, 20), (22, 24), (31, 32)] []))
  (.leafAt [((sp [(1, (-1)), (15, 1)] 0), .fact 13), ((sp [(1, 1), (15, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(15, 28), (18, 20), (22, 24), (31, 32)] []))
  (.leafAt [((sp [(7, (-1))] 2), .atom 0), ((sp [(7, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(15, 28), (18, 20), (22, 24), (31, 32)] []))
  (.leafAt [((sp [(1, (-1)), (28, 1)] 0), .fact 15), ((sp [(1, 1), (28, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(1, (-1)), (28, 1)] 0), .fact 15), ((sp [(1, 1), (28, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def admit_l3 : MLaw := ⟨.le (.get 3 (.var 8)) (.var 2), some 8⟩
def admit_e3 : MEntry := ⟨admit_l3, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10], .leafAt [((sp [(2, 1)] 1), .fact 0), ((sp [(2, (-1))] 0), .nat 2)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .term (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 3 (.var 6)) (.const 1)) (.get 3 (.var 6))), .term (.ite (.eq (.var 9) (.var 6)) (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 3 (.var 6)) (.const 1)) (.get 3 (.var 6))) (.get 3 (.var 9))), .cell 0 (sp [(3, 1)] 0), .cell 1 (sp [(4, 1)] 0), .cell 2 (sp [(5, 1)] 0), .cell 3 (sp [(6, 1)] 0), .cell 0 (sp [(4, 1)] 0), .cell 0 (sp [(5, 1)] 0), .cell 0 (sp [(6, 1)] 0), .cell 0 (sp [(9, 1)] 0), .cell 1 (sp [(3, 1)] 0), .cell 1 (sp [(5, 1)] 0), .cell 1 (sp [(6, 1)] 0), .cell 1 (sp [(9, 1)] 0), .cell 2 (sp [(3, 1)] 0), .cell 2 (sp [(4, 1)] 0), .cell 2 (sp [(6, 1)] 0), .cell 2 (sp [(9, 1)] 0), .cell 3 (sp [(3, 1)] 0), .cell 3 (sp [(4, 1)] 0), .cell 3 (sp [(5, 1)] 0), .cell 3 (sp [(9, 1)] 0)], .split (sp [(6, (-1)), (9, 1)] 0)
  (.split (sp [(6, 1), (9, (-1))] 0)
  (.split (sp [(7, 1)] (-1))
  (.split (sp [(7, (-1))] 1)
  (.split (sp [(13, 1)] 0)
  (.split (sp [(0, (-1)), (14, 1)] 1)
  (.split (sp [(1, (-1)), (15, 1)] 1)
  (.split (sp [(2, (-1)), (16, 1)] 1)
  (.leafAt [((sp [] 1), .fact 21)] [.input 0] [(16, 32), (19, 20), (23, 24), (27, 28)] [])
  (.leafAt [((sp [(2, (-1)), (16, 1)] 0), .fact 19), ((sp [(2, 1), (16, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(16, 32), (19, 20), (23, 24), (27, 28)] []))
  (.leafAt [((sp [(2, (-1)), (16, 1)] 0), .fact 19), ((sp [(2, 1), (16, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(16, 32), (19, 20), (23, 24), (27, 28)] []))
  (.leafAt [((sp [(2, (-1)), (16, 1)] 0), .fact 19), ((sp [(2, 1), (16, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(16, 32), (19, 20), (23, 24), (27, 28)] []))
  (.leafAt [((sp [(2, (-1)), (16, 1)] 0), .fact 19), ((sp [(2, 1), (16, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(16, 32), (19, 20), (23, 24), (27, 28)] []))
  (.leafAt [((sp [(2, (-1)), (16, 1)] 0), .fact 19), ((sp [(2, 1), (16, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(16, 32), (19, 20), (23, 24), (27, 28)] []))
  (.leafAt [((sp [(7, (-1))] 2), .atom 0), ((sp [(7, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(16, 32), (19, 20), (23, 24), (27, 28)] []))
  (.leafAt [((sp [(2, (-1)), (32, 1)] 0), .fact 20), ((sp [(2, 1), (32, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(2, (-1)), (32, 1)] 0), .fact 20), ((sp [(2, 1), (32, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def admit_proof : List MEntry := [admit_e0, admit_e1, admit_e2, admit_e3]
theorem admit_check : checkFMMachine admit_machine admit_proof = true := by decide +kernel
theorem admit_laws : ∀ ρ M, FMReach admit_machine ρ M → ∀ e ∈ admit_proof, e.law.Holds ρ M :=
  fmmachine_sound admit_machine admit_proof admit_check
namespace admit
abbrev «d» : Nat := 0
abbrev «hr» : Nat := 1
abbrev «dm» : Nat := 2
abbrev «Acct» : Nat := 0
abbrev «Day» : Nat := 1
abbrev «Hour» : Nat := 2
abbrev «Dom» : Nat := 3
/-- once_per_account: every Acct count <= its cap -/
theorem law0 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach admit_machine ρ μ) : ∀ k : Nat, (μ «Acct» (k)) ≤ 1 := by
  have hl : admit_l0.Holds ρ μ := admit_laws ρ μ h admit_e0 (by simp [admit_proof])
  exact fun k => (evalC_iff (upd ρ 8 k) μ admit_l0.holds).mp (hl k)
/-- day_cap: every Day count <= its cap -/
theorem law1 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach admit_machine ρ μ) : ∀ k : Nat, (μ «Day» (k)) ≤ ρ «d» := by
  have hl : admit_l1.Holds ρ μ := admit_laws ρ μ h admit_e1 (by simp [admit_proof])
  exact fun k => (evalC_iff (upd ρ 8 k) μ admit_l1.holds).mp (hl k)
/-- hour_cap: every Hour count <= its cap -/
theorem law2 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach admit_machine ρ μ) : ∀ k : Nat, (μ «Hour» (k)) ≤ ρ «hr» := by
  have hl : admit_l2.Holds ρ μ := admit_laws ρ μ h admit_e2 (by simp [admit_proof])
  exact fun k => (evalC_iff (upd ρ 8 k) μ admit_l2.holds).mp (hl k)
/-- dom_cap: every Dom count <= its cap -/
theorem law3 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach admit_machine ρ μ) : ∀ k : Nat, (μ «Dom» (k)) ≤ ρ «dm» := by
  have hl : admit_l3.Holds ρ μ := admit_laws ρ μ h admit_e3 (by simp [admit_proof])
  exact fun k => (evalC_iff (upd ρ 8 k) μ admit_l3.holds).mp (hl k)
end admit
-- the caps rule's day cap in plain Lean: in every reachable state, every Day count is at most d (variable 0; Day is map 1).
theorem day_cap (ρ : Nat → Nat) (M : Nat → Nat → Nat) (h : FMReach admit_machine ρ M) (k : Nat) : M 1 k ≤ ρ 0 :=
  admit.law1 ρ M h k
-- TAMPERED: the admit proof offered for the machine whose Day cap is unguarded. Lean computes the check to false.
def admit_tampered : FMMachine := ⟨⟨[3, 4, 5, 6, 7],
  [],
  [(0, 0), (1, 0), (2, 0), (3, 0)],
  [],
  [(0, .var 3, .ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2))))) (.add (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3))), (1, .var 4, .ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2))))) (.add (.get 1 (.var 4)) (.const 1)) (.get 1 (.var 4))), (2, .var 5, .ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2))))) (.add (.get 2 (.var 5)) (.const 1)) (.get 2 (.var 5))), (3, .var 6, .ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2))))) (.add (.get 3 (.var 6)) (.const 1)) (.get 3 (.var 6)))],
  .le (.const 0) (.const 0),
  .or (.eq (.var 7) (.const 0)) (.eq (.var 7) (.const 1))⟩,
  []⟩
example : checkFMMachine admit_tampered admit_proof = false := by decide +kernel

-- loss, guard as a flag: bounded_loss: s <= b + m, with flags room  (variables 0 b, 1 m, 2 c, 3 s, 4 ?room)
def fpolicy_machine : FMachine := ⟨⟨[2],
  [(3, .const 0)],
  [(3, .ite (.eq (.var 4) (.const 1)) (.add (.var 3) (.min (.var 2) (.var 1))) (.var 3))],
  .le (.const 0) (.const 0),
  .le (.const 0) (.const 0)⟩,
  [(4, .lt (.var 3) (.var 0))]⟩
def fpolicy_proof : MachineProof := [(.le (.var 3) (.add (.var 0) (.var 1)),
  ([.var 0, .var 1, .var 2, .var 3, .var 4], .leafAt [((sp [(0, 1), (1, 1)] 1), .fact 0), ((sp [(0, (-1))] 0), .nat 0), ((sp [(1, (-1))] 0), .nat 1)] [.input 0, .input 1, .input 2, .combine 0 1 1 1, .combine 3 2 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .term (.min (.var 2) (.var 1)), .term (.ite (.lt (.var 3) (.var 0)) (.add (.var 3) (.min (.var 2) (.var 1))) (.var 3))], .split (sp [(0, (-1)), (3, 1)] 1)
  (.split (sp [(1, (-1)), (2, 1)] 0)
  (.leafAt [((sp [(0, (-1)), (3, 1)] 1), .atom 1), ((sp [(1, (-1)), (2, 1)] 0), .atom 0), ((sp [(0, 1), (1, 1), (2, (-1)), (3, (-1))] 1), .fact 1)] [.input 0, .input 1, .input 2, .combine 2 0 1 1, .combine 1 3 1 1] [] [])
  (.leafAt [((sp [(0, (-1)), (3, 1)] 1), .atom 1), ((sp [(0, 1), (3, (-1))] 1), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(0, (-1)), (1, (-1)), (3, 1)] 0), .fact 0), ((sp [(0, 1), (1, 1), (3, (-1))] 1), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))]
theorem fpolicy_laws : ∀ maps ρ, FReach fpolicy_machine maps ρ → ∀ l ∈ fpolicy_proof.map (·.1), evalC ρ maps l = true :=
  fmachine_sound fpolicy_machine fpolicy_proof (by decide +kernel)
-- TAMPERED: the proof offered for the machine whose flag always admits (room := 0 <= 0). Lean computes the check to false.
def fpolicy_tampered : FMachine := { fpolicy_machine with flags := [(4, .le (.const 0) (.const 0))] }
example : checkFMachine fpolicy_tampered fpolicy_proof = false := by decide +kernel

-- admit: once_per_account: every Acct count <= its cap; day_cap: every Day count <= its cap; hour_cap: every Hour count <= its cap; dom_cap: every Dom count <= its cap, with flags granted  (variables 0 d, 1 hr, 2 dm, 3 acct, 4 day, 5 hour, 6 dom, 7 ok, 8 k, 9 k#, 10 #, 11 ?granted; maps 0 Acct, 1 Day, 2 Hour, 3 Dom)
def fadmit_machine : FMMachine := ⟨⟨[3, 4, 5, 6, 7],
  [],
  [(0, 0), (1, 0), (2, 0), (3, 0)],
  [],
  [(0, .var 3, .ite (.eq (.var 11) (.const 1)) (.add (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3))), (1, .var 4, .ite (.eq (.var 11) (.const 1)) (.add (.get 1 (.var 4)) (.const 1)) (.get 1 (.var 4))), (2, .var 5, .ite (.eq (.var 11) (.const 1)) (.add (.get 2 (.var 5)) (.const 1)) (.get 2 (.var 5))), (3, .var 6, .ite (.eq (.var 11) (.const 1)) (.add (.get 3 (.var 6)) (.const 1)) (.get 3 (.var 6)))],
  .le (.const 0) (.const 0),
  .or (.eq (.var 7) (.const 0)) (.eq (.var 7) (.const 1))⟩,
  [(11, .and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2))))))]⟩
def fadmit_l0 : MLaw := ⟨.le (.get 0 (.var 8)) (.const 1), some 8⟩
def fadmit_e0 : MEntry := ⟨fadmit_l0, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11], .leafAt [((sp [] 1), .fact 0)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .term (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3))), .term (.ite (.eq (.var 9) (.var 3)) (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3))) (.get 0 (.var 9))), .cell 0 (sp [(3, 1)] 0), .cell 1 (sp [(4, 1)] 0), .cell 2 (sp [(5, 1)] 0), .cell 3 (sp [(6, 1)] 0), .cell 0 (sp [(4, 1)] 0), .cell 0 (sp [(5, 1)] 0), .cell 0 (sp [(6, 1)] 0), .cell 0 (sp [(9, 1)] 0), .cell 1 (sp [(3, 1)] 0), .cell 1 (sp [(5, 1)] 0), .cell 1 (sp [(6, 1)] 0), .cell 1 (sp [(9, 1)] 0), .cell 2 (sp [(3, 1)] 0), .cell 2 (sp [(4, 1)] 0), .cell 2 (sp [(6, 1)] 0), .cell 2 (sp [(9, 1)] 0), .cell 3 (sp [(3, 1)] 0), .cell 3 (sp [(4, 1)] 0), .cell 3 (sp [(5, 1)] 0), .cell 3 (sp [(9, 1)] 0)], .split (sp [(3, (-1)), (9, 1)] 0)
  (.split (sp [(3, 1), (9, (-1))] 0)
  (.split (sp [(7, 1)] (-1))
  (.split (sp [(7, (-1))] 1)
  (.split (sp [(14, 1)] 0)
  (.split (sp [(0, (-1)), (15, 1)] 1)
  (.split (sp [(1, (-1)), (16, 1)] 1)
  (.split (sp [(2, (-1)), (17, 1)] 1)
  (.leafAt [((sp [] 1), .fact 21)] [.input 0] [(14, 21), (22, 25), (26, 29), (30, 33)] [])
  (.leafAt [((sp [(14, 1)] 0), .atom 3), ((sp [(14, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(14, 21), (22, 25), (26, 29), (30, 33)] []))
  (.leafAt [((sp [(14, 1)] 0), .atom 2), ((sp [(14, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(14, 21), (22, 25), (26, 29), (30, 33)] []))
  (.leafAt [((sp [(14, 1)] 0), .atom 1), ((sp [(14, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(14, 21), (22, 25), (26, 29), (30, 33)] []))
  (.leafAt [((sp [(14, 1)] (-1)), .fact 1), ((sp [(14, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(14, 21), (22, 25), (26, 29), (30, 33)] []))
  (.leafAt [((sp [(14, 1)] (-1)), .fact 1), ((sp [(14, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(14, 21), (22, 25), (26, 29), (30, 33)] []))
  (.leafAt [((sp [(7, (-1))] 2), .atom 0), ((sp [(7, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(14, 21), (22, 25), (26, 29), (30, 33)] []))
  (.leafAt [((sp [(21, 1)] (-1)), .fact 5), ((sp [(21, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(21, 1)] (-1)), .fact 5), ((sp [(21, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def fadmit_l1 : MLaw := ⟨.le (.get 1 (.var 8)) (.var 0), some 8⟩
def fadmit_e1 : MEntry := ⟨fadmit_l1, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11], .leafAt [((sp [(0, 1)] 1), .fact 0), ((sp [(0, (-1))] 0), .nat 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .term (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 1 (.var 4)) (.const 1)) (.get 1 (.var 4))), .term (.ite (.eq (.var 9) (.var 4)) (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 1 (.var 4)) (.const 1)) (.get 1 (.var 4))) (.get 1 (.var 9))), .cell 0 (sp [(3, 1)] 0), .cell 1 (sp [(4, 1)] 0), .cell 2 (sp [(5, 1)] 0), .cell 3 (sp [(6, 1)] 0), .cell 0 (sp [(4, 1)] 0), .cell 0 (sp [(5, 1)] 0), .cell 0 (sp [(6, 1)] 0), .cell 0 (sp [(9, 1)] 0), .cell 1 (sp [(3, 1)] 0), .cell 1 (sp [(5, 1)] 0), .cell 1 (sp [(6, 1)] 0), .cell 1 (sp [(9, 1)] 0), .cell 2 (sp [(3, 1)] 0), .cell 2 (sp [(4, 1)] 0), .cell 2 (sp [(6, 1)] 0), .cell 2 (sp [(9, 1)] 0), .cell 3 (sp [(3, 1)] 0), .cell 3 (sp [(4, 1)] 0), .cell 3 (sp [(5, 1)] 0), .cell 3 (sp [(9, 1)] 0)], .split (sp [(4, (-1)), (9, 1)] 0)
  (.split (sp [(4, 1), (9, (-1))] 0)
  (.split (sp [(7, 1)] (-1))
  (.split (sp [(7, (-1))] 1)
  (.split (sp [(14, 1)] 0)
  (.split (sp [(0, (-1)), (15, 1)] 1)
  (.split (sp [(1, (-1)), (16, 1)] 1)
  (.split (sp [(2, (-1)), (17, 1)] 1)
  (.leafAt [((sp [] 1), .fact 21)] [.input 0] [(15, 25), (18, 21), (27, 29), (31, 33)] [])
  (.leafAt [((sp [(0, (-1)), (15, 1)] 1), .atom 2), ((sp [(0, 1), (15, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(15, 25), (18, 21), (27, 29), (31, 33)] []))
  (.leafAt [((sp [(0, (-1)), (15, 1)] 1), .atom 1), ((sp [(0, 1), (15, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(15, 25), (18, 21), (27, 29), (31, 33)] []))
  (.leafAt [((sp [(0, (-1)), (15, 1)] 0), .fact 7), ((sp [(0, 1), (15, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(15, 25), (18, 21), (27, 29), (31, 33)] []))
  (.leafAt [((sp [(0, (-1)), (15, 1)] 0), .fact 7), ((sp [(0, 1), (15, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(15, 25), (18, 21), (27, 29), (31, 33)] []))
  (.leafAt [((sp [(0, (-1)), (15, 1)] 0), .fact 7), ((sp [(0, 1), (15, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(15, 25), (18, 21), (27, 29), (31, 33)] []))
  (.leafAt [((sp [(7, (-1))] 2), .atom 0), ((sp [(7, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(15, 25), (18, 21), (27, 29), (31, 33)] []))
  (.leafAt [((sp [(0, (-1)), (25, 1)] 0), .fact 10), ((sp [(0, 1), (25, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(0, (-1)), (25, 1)] 0), .fact 10), ((sp [(0, 1), (25, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def fadmit_l2 : MLaw := ⟨.le (.get 2 (.var 8)) (.var 1), some 8⟩
def fadmit_e2 : MEntry := ⟨fadmit_l2, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11], .leafAt [((sp [(1, 1)] 1), .fact 0), ((sp [(1, (-1))] 0), .nat 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .term (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 2 (.var 5)) (.const 1)) (.get 2 (.var 5))), .term (.ite (.eq (.var 9) (.var 5)) (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 2 (.var 5)) (.const 1)) (.get 2 (.var 5))) (.get 2 (.var 9))), .cell 0 (sp [(3, 1)] 0), .cell 1 (sp [(4, 1)] 0), .cell 2 (sp [(5, 1)] 0), .cell 3 (sp [(6, 1)] 0), .cell 0 (sp [(4, 1)] 0), .cell 0 (sp [(5, 1)] 0), .cell 0 (sp [(6, 1)] 0), .cell 0 (sp [(9, 1)] 0), .cell 1 (sp [(3, 1)] 0), .cell 1 (sp [(5, 1)] 0), .cell 1 (sp [(6, 1)] 0), .cell 1 (sp [(9, 1)] 0), .cell 2 (sp [(3, 1)] 0), .cell 2 (sp [(4, 1)] 0), .cell 2 (sp [(6, 1)] 0), .cell 2 (sp [(9, 1)] 0), .cell 3 (sp [(3, 1)] 0), .cell 3 (sp [(4, 1)] 0), .cell 3 (sp [(5, 1)] 0), .cell 3 (sp [(9, 1)] 0)], .split (sp [(5, (-1)), (9, 1)] 0)
  (.split (sp [(5, 1), (9, (-1))] 0)
  (.split (sp [(7, 1)] (-1))
  (.split (sp [(7, (-1))] 1)
  (.split (sp [(14, 1)] 0)
  (.split (sp [(0, (-1)), (15, 1)] 1)
  (.split (sp [(1, (-1)), (16, 1)] 1)
  (.split (sp [(2, (-1)), (17, 1)] 1)
  (.leafAt [((sp [] 1), .fact 21)] [.input 0] [(16, 29), (19, 21), (23, 25), (32, 33)] [])
  (.leafAt [((sp [(1, (-1)), (16, 1)] 1), .atom 1), ((sp [(1, 1), (16, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(16, 29), (19, 21), (23, 25), (32, 33)] []))
  (.leafAt [((sp [(1, (-1)), (16, 1)] 0), .fact 13), ((sp [(1, 1), (16, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(16, 29), (19, 21), (23, 25), (32, 33)] []))
  (.leafAt [((sp [(1, (-1)), (16, 1)] 0), .fact 13), ((sp [(1, 1), (16, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(16, 29), (19, 21), (23, 25), (32, 33)] []))
  (.leafAt [((sp [(1, (-1)), (16, 1)] 0), .fact 13), ((sp [(1, 1), (16, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(16, 29), (19, 21), (23, 25), (32, 33)] []))
  (.leafAt [((sp [(1, (-1)), (16, 1)] 0), .fact 13), ((sp [(1, 1), (16, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(16, 29), (19, 21), (23, 25), (32, 33)] []))
  (.leafAt [((sp [(7, (-1))] 2), .atom 0), ((sp [(7, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(16, 29), (19, 21), (23, 25), (32, 33)] []))
  (.leafAt [((sp [(1, (-1)), (29, 1)] 0), .fact 15), ((sp [(1, 1), (29, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(1, (-1)), (29, 1)] 0), .fact 15), ((sp [(1, 1), (29, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def fadmit_l3 : MLaw := ⟨.le (.get 3 (.var 8)) (.var 2), some 8⟩
def fadmit_e3 : MEntry := ⟨fadmit_l3, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11], .leafAt [((sp [(2, 1)] 1), .fact 0), ((sp [(2, (-1))] 0), .nat 2)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .term (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 3 (.var 6)) (.const 1)) (.get 3 (.var 6))), .term (.ite (.eq (.var 9) (.var 6)) (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 3 (.var 6)) (.const 1)) (.get 3 (.var 6))) (.get 3 (.var 9))), .cell 0 (sp [(3, 1)] 0), .cell 1 (sp [(4, 1)] 0), .cell 2 (sp [(5, 1)] 0), .cell 3 (sp [(6, 1)] 0), .cell 0 (sp [(4, 1)] 0), .cell 0 (sp [(5, 1)] 0), .cell 0 (sp [(6, 1)] 0), .cell 0 (sp [(9, 1)] 0), .cell 1 (sp [(3, 1)] 0), .cell 1 (sp [(5, 1)] 0), .cell 1 (sp [(6, 1)] 0), .cell 1 (sp [(9, 1)] 0), .cell 2 (sp [(3, 1)] 0), .cell 2 (sp [(4, 1)] 0), .cell 2 (sp [(6, 1)] 0), .cell 2 (sp [(9, 1)] 0), .cell 3 (sp [(3, 1)] 0), .cell 3 (sp [(4, 1)] 0), .cell 3 (sp [(5, 1)] 0), .cell 3 (sp [(9, 1)] 0)], .split (sp [(6, (-1)), (9, 1)] 0)
  (.split (sp [(6, 1), (9, (-1))] 0)
  (.split (sp [(7, 1)] (-1))
  (.split (sp [(7, (-1))] 1)
  (.split (sp [(14, 1)] 0)
  (.split (sp [(0, (-1)), (15, 1)] 1)
  (.split (sp [(1, (-1)), (16, 1)] 1)
  (.split (sp [(2, (-1)), (17, 1)] 1)
  (.leafAt [((sp [] 1), .fact 21)] [.input 0] [(17, 33), (20, 21), (24, 25), (28, 29)] [])
  (.leafAt [((sp [(2, (-1)), (17, 1)] 0), .fact 19), ((sp [(2, 1), (17, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(17, 33), (20, 21), (24, 25), (28, 29)] []))
  (.leafAt [((sp [(2, (-1)), (17, 1)] 0), .fact 19), ((sp [(2, 1), (17, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(17, 33), (20, 21), (24, 25), (28, 29)] []))
  (.leafAt [((sp [(2, (-1)), (17, 1)] 0), .fact 19), ((sp [(2, 1), (17, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(17, 33), (20, 21), (24, 25), (28, 29)] []))
  (.leafAt [((sp [(2, (-1)), (17, 1)] 0), .fact 19), ((sp [(2, 1), (17, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(17, 33), (20, 21), (24, 25), (28, 29)] []))
  (.leafAt [((sp [(2, (-1)), (17, 1)] 0), .fact 19), ((sp [(2, 1), (17, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(17, 33), (20, 21), (24, 25), (28, 29)] []))
  (.leafAt [((sp [(7, (-1))] 2), .atom 0), ((sp [(7, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(17, 33), (20, 21), (24, 25), (28, 29)] []))
  (.leafAt [((sp [(2, (-1)), (33, 1)] 0), .fact 20), ((sp [(2, 1), (33, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(2, (-1)), (33, 1)] 0), .fact 20), ((sp [(2, 1), (33, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def fadmit_proof : List MEntry := [fadmit_e0, fadmit_e1, fadmit_e2, fadmit_e3]
theorem fadmit_check : checkFMMachine fadmit_machine fadmit_proof = true := by decide +kernel
theorem fadmit_laws : ∀ ρ M, FMReach fadmit_machine ρ M → ∀ e ∈ fadmit_proof, e.law.Holds ρ M :=
  fmmachine_sound fadmit_machine fadmit_proof fadmit_check
namespace fadmit
abbrev «d» : Nat := 0
abbrev «hr» : Nat := 1
abbrev «dm» : Nat := 2
abbrev «Acct» : Nat := 0
abbrev «Day» : Nat := 1
abbrev «Hour» : Nat := 2
abbrev «Dom» : Nat := 3
/-- once_per_account: every Acct count <= its cap -/
theorem law0 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach fadmit_machine ρ μ) : ∀ k : Nat, (μ «Acct» (k)) ≤ 1 := by
  have hl : fadmit_l0.Holds ρ μ := fadmit_laws ρ μ h fadmit_e0 (by simp [fadmit_proof])
  exact fun k => (evalC_iff (upd ρ 8 k) μ fadmit_l0.holds).mp (hl k)
/-- day_cap: every Day count <= its cap -/
theorem law1 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach fadmit_machine ρ μ) : ∀ k : Nat, (μ «Day» (k)) ≤ ρ «d» := by
  have hl : fadmit_l1.Holds ρ μ := fadmit_laws ρ μ h fadmit_e1 (by simp [fadmit_proof])
  exact fun k => (evalC_iff (upd ρ 8 k) μ fadmit_l1.holds).mp (hl k)
/-- hour_cap: every Hour count <= its cap -/
theorem law2 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach fadmit_machine ρ μ) : ∀ k : Nat, (μ «Hour» (k)) ≤ ρ «hr» := by
  have hl : fadmit_l2.Holds ρ μ := fadmit_laws ρ μ h fadmit_e2 (by simp [fadmit_proof])
  exact fun k => (evalC_iff (upd ρ 8 k) μ fadmit_l2.holds).mp (hl k)
/-- dom_cap: every Dom count <= its cap -/
theorem law3 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach fadmit_machine ρ μ) : ∀ k : Nat, (μ «Dom» (k)) ≤ ρ «dm» := by
  have hl : fadmit_l3.Holds ρ μ := fadmit_laws ρ μ h fadmit_e3 (by simp [fadmit_proof])
  exact fun k => (evalC_iff (upd ρ 8 k) μ fadmit_l3.holds).mp (hl k)
end fadmit
-- TAMPERED: the flagged admit proof offered for a grant flag without the Day cap. Lean computes the check to false.
def fadmit_tampered : FMMachine := ⟨⟨[3, 4, 5, 6, 7],
  [],
  [(0, 0), (1, 0), (2, 0), (3, 0)],
  [],
  [(0, .var 3, .ite (.eq (.var 11) (.const 1)) (.add (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3))), (1, .var 4, .ite (.eq (.var 11) (.const 1)) (.add (.get 1 (.var 4)) (.const 1)) (.get 1 (.var 4))), (2, .var 5, .ite (.eq (.var 11) (.const 1)) (.add (.get 2 (.var 5)) (.const 1)) (.get 2 (.var 5))), (3, .var 6, .ite (.eq (.var 11) (.const 1)) (.add (.get 3 (.var 6)) (.const 1)) (.get 3 (.var 6)))],
  .le (.const 0) (.const 0),
  .or (.eq (.var 7) (.const 0)) (.eq (.var 7) (.const 1))⟩,
  [(11, .and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))]⟩
example : checkFMMachine fadmit_tampered fadmit_proof = false := by decide +kernel

-- meter, counting down refines meter: left + used = cap, with flags b_fits  (variables 0 cap, 1 most, 2 amount, 3 a_left, 4 b_used, 5 #, 6 ?b_fits, 7 a_left', 8 b_used'; maps )
def refines_machine : FMMachine := ⟨⟨[2],
  [(3, .var 0), (4, .const 0)],
  [],
  [(3, .ite (.le (.min (.var 2) (.var 1)) (.var 3)) (.sub (.var 3) (.min (.var 2) (.var 1))) (.var 3)), (4, .ite (.eq (.var 6) (.const 1)) (.add (.var 4) (.min (.var 2) (.var 1))) (.var 4))],
  [],
  .le (.const 0) (.const 0),
  .le (.const 0) (.const 0)⟩,
  [(6, .le (.add (.var 4) (.min (.var 2) (.var 1))) (.var 0))]⟩
def refines_l0 : MLaw := ⟨.eq (.add (.var 3) (.var 4)) (.var 0), none⟩
def refines_e0 : MEntry := ⟨refines_l0, 5, [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8], .leafAt [((sp [] 1), .fact 0)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .term (.min (.var 2) (.var 1)), .term (.sub (.var 3) (.min (.var 2) (.var 1))), .term (.ite (.le (.min (.var 2) (.var 1)) (.var 3)) (.sub (.var 3) (.min (.var 2) (.var 1))) (.var 3)), .term (.ite (.le (.add (.var 4) (.min (.var 2) (.var 1))) (.var 0)) (.add (.var 4) (.min (.var 2) (.var 1))) (.var 4))], .split (sp [(1, (-1)), (2, 1)] 0)
  (.split (sp [(2, 1), (3, (-1))] 0)
  (.split (sp [(0, (-1)), (2, 1), (4, 1)] 0)
  (.split (sp [(0, (-1)), (3, 1), (4, 1)] 0)
  (.leafAt [((sp [(0, 1), (3, (-1)), (4, (-1))] 0), .fact 0), ((sp [(0, (-1)), (3, 1), (4, 1)] 1), .fact 1)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(0, 1), (3, (-1)), (4, (-1))] 1), .atom 0), ((sp [(0, (-1)), (3, 1), (4, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(2, 1), (3, (-1))] 0), .atom 1), ((sp [(0, 1), (2, (-1)), (4, (-1))] 1), .atom 0), ((sp [(0, (-1)), (3, 1), (4, 1)] 0), .fact 0)] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 3 1 1 1] [] []))
  (.split (sp [(0, (-1)), (2, 1), (4, 1)] 0)
  (.leafAt [((sp [(2, (-1)), (3, 1)] 1), .atom 1), ((sp [(0, (-1)), (2, 1), (4, 1)] 0), .atom 0), ((sp [(0, 1), (3, (-1)), (4, (-1))] 0), .fact 0)] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 1 3 1 1] [] [])
  (.split (sp [(0, (-1)), (3, 1), (4, 1)] 0)
  (.leafAt [((sp [(0, 1), (3, (-1)), (4, (-1))] 0), .fact 0), ((sp [(0, (-1)), (3, 1), (4, 1)] 1), .fact 1)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(0, 1), (3, (-1)), (4, (-1))] 1), .atom 0), ((sp [(0, (-1)), (3, 1), (4, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []))))
  (.split (sp [(1, 1), (3, (-1))] 0)
  (.split (sp [(0, (-1)), (1, 1), (4, 1)] 0)
  (.split (sp [(0, (-1)), (3, 1), (4, 1)] 0)
  (.leafAt [((sp [(0, 1), (3, (-1)), (4, (-1))] 0), .fact 0), ((sp [(0, (-1)), (3, 1), (4, 1)] 1), .fact 1)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(0, 1), (3, (-1)), (4, (-1))] 1), .atom 0), ((sp [(0, (-1)), (3, 1), (4, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(1, 1), (3, (-1))] 0), .atom 1), ((sp [(0, 1), (1, (-1)), (4, (-1))] 1), .atom 0), ((sp [(0, (-1)), (3, 1), (4, 1)] 0), .fact 0)] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 3 1 1 1] [] []))
  (.split (sp [(0, (-1)), (1, 1), (4, 1)] 0)
  (.leafAt [((sp [(1, (-1)), (3, 1)] 1), .atom 1), ((sp [(0, (-1)), (1, 1), (4, 1)] 0), .atom 0), ((sp [(0, 1), (3, (-1)), (4, (-1))] 0), .fact 0)] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 1 3 1 1] [] [])
  (.split (sp [(0, (-1)), (3, 1), (4, 1)] 0)
  (.leafAt [((sp [(0, 1), (3, (-1)), (4, (-1))] 0), .fact 0), ((sp [(0, (-1)), (3, 1), (4, 1)] 1), .fact 1)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(0, 1), (3, (-1)), (4, (-1))] 1), .atom 0), ((sp [(0, (-1)), (3, 1), (4, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))))⟩
def refines_proof : List MEntry := [refines_e0]
theorem refines_check : checkFMMachine refines_machine refines_proof = true := by decide +kernel
theorem refines_laws : ∀ ρ M, FMReach refines_machine ρ M → ∀ e ∈ refines_proof, e.law.Holds ρ M :=
  fmmachine_sound refines_machine refines_proof refines_check
namespace refines
abbrev «cap» : Nat := 0
abbrev «a_left» : Nat := 3
abbrev «b_used» : Nat := 4
/-- left + used = cap -/
theorem law0 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach refines_machine ρ μ) : (ρ «a_left» + ρ «b_used») = ρ «cap» := by
  have hl : refines_l0.Holds ρ μ := refines_laws ρ μ h refines_e0 (by simp [refines_proof])
  exact (evalC_iff ρ μ refines_l0.holds).mp hl
end refines

-- Step law: meter allows the request it is sent
def refines_step0 : StepLaw := ⟨.le (.const 0) (.const 0),
  .le (.min (.var 2) (.var 1)) (.var 1),
  [(3, 7), (4, 8)],
  [],
  [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .term (.min (.var 2) (.var 1))], .split (sp [(1, (-1)), (2, 1)] 0)
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] [])
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] []))⟩
theorem refines_step0_holds : StepLawHolds refines_machine refines_step0 :=
  steplaw_sound refines_machine refines_proof refines_step0 refines_check (by decide +kernel)

-- counter || counter: a.n <= cap; b.n <= cap, with sets (carried none; quantified flags none)
--   (variables 0 cap, 1 amount, 2 turn, 3 a_n, 4 b_n, 5 #, 6 a_n', 7 b_n', 8 amount@2, 9 turn@2, 10 a_n~1, 11 b_n~1; maps )
def interleaved_machine : SMachine := ⟨⟨⟨[1, 2],
  [(3, .const 0), (4, .const 0)],
  [],
  [(3, .ite (.eq (.var 2) (.const 1)) (.var 3) (.ite (.le (.add (.var 3) (.var 1)) (.var 0)) (.add (.var 3) (.var 1)) (.var 3))), (4, .ite (.eq (.var 2) (.const 0)) (.var 4) (.ite (.le (.add (.var 4) (.var 1)) (.var 0)) (.add (.var 4) (.var 1)) (.var 4)))],
  [],
  .and (.le (.var 0) (.const 10)) (.le (.var 0) (.const 10)),
  .or (.eq (.var 2) (.const 0)) (.eq (.var 2) (.const 1))⟩,
  []⟩,
  [],
  [],
  [],
  [],
  [],
  []⟩
def interleaved_l0 : MLaw := ⟨.le (.var 3) (.var 0), none⟩
def interleaved_e0 : SEntry := ⟨interleaved_l0, 5, [], [], [], [], [], [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11], [.and (.le (.var 0) (.const 10)) (.le (.var 0) (.const 10)), .not (.le (.const 0) (.var 0))], .leafAt [((sp [(0, 1)] 1), .fact 1), ((sp [(0, (-1))] 0), .nat 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .term (.ite (.le (.add (.var 3) (.var 1)) (.var 0)) (.add (.var 3) (.var 1)) (.var 3)), .term (.ite (.eq (.var 2) (.const 1)) (.var 3) (.ite (.le (.add (.var 3) (.var 1)) (.var 0)) (.add (.var 3) (.var 1)) (.var 3)))], [.and (.le (.var 0) (.const 10)) (.le (.var 0) (.const 10)), .or (.eq (.var 2) (.const 0)) (.eq (.var 2) (.const 1)), .le (.var 3) (.var 0), .le (.var 4) (.var 0), .not (.le (.ite (.eq (.var 2) (.const 1)) (.var 3) (.ite (.le (.add (.var 3) (.var 1)) (.var 0)) (.add (.var 3) (.var 1)) (.var 3))) (.var 0))], .split (sp [(2, 1)] (-1))
  (.split (sp [(2, (-1))] 1)
  (.leafAt [((sp [(0, (-1)), (3, 1)] 0), .fact 2), ((sp [(0, 1), (3, (-1))] 1), .fact 4)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.split (sp [(0, (-1)), (1, 1), (3, 1)] 0)
  (.leafAt [((sp [] 1), .fact 4)] [.input 0] [] [])
  (.leafAt [((sp [(0, (-1)), (3, 1)] 0), .fact 2), ((sp [(0, 1), (3, (-1))] 1), .fact 4)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))
  (.leafAt [((sp [(2, (-1))] 2), .atom 0), ((sp [(2, 1)] 0), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def interleaved_l1 : MLaw := ⟨.le (.var 4) (.var 0), none⟩
def interleaved_e1 : SEntry := ⟨interleaved_l1, 5, [], [], [], [], [], [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11], [.and (.le (.var 0) (.const 10)) (.le (.var 0) (.const 10)), .not (.le (.const 0) (.var 0))], .leafAt [((sp [(0, 1)] 1), .fact 1), ((sp [(0, (-1))] 0), .nat 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .term (.ite (.le (.add (.var 4) (.var 1)) (.var 0)) (.add (.var 4) (.var 1)) (.var 4)), .term (.ite (.eq (.var 2) (.const 0)) (.var 4) (.ite (.le (.add (.var 4) (.var 1)) (.var 0)) (.add (.var 4) (.var 1)) (.var 4)))], [.and (.le (.var 0) (.const 10)) (.le (.var 0) (.const 10)), .or (.eq (.var 2) (.const 0)) (.eq (.var 2) (.const 1)), .le (.var 3) (.var 0), .le (.var 4) (.var 0), .not (.le (.ite (.eq (.var 2) (.const 0)) (.var 4) (.ite (.le (.add (.var 4) (.var 1)) (.var 0)) (.add (.var 4) (.var 1)) (.var 4))) (.var 0))], .split (sp [(2, 1)] 0)
  (.split (sp [(2, (-1))] 0)
  (.leafAt [((sp [(0, (-1)), (4, 1)] 0), .fact 3), ((sp [(0, 1), (4, (-1))] 1), .fact 4)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leafAt [((sp [] 1), .fact 1)] [.input 0] [] []))
  (.split (sp [(0, (-1)), (1, 1), (4, 1)] 0)
  (.leafAt [((sp [] 1), .fact 4)] [.input 0] [] [])
  (.leafAt [((sp [(0, (-1)), (4, 1)] 0), .fact 3), ((sp [(0, 1), (4, (-1))] 1), .fact 4)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩
def interleaved_proof : List SEntry := [interleaved_e0, interleaved_e1]
theorem interleaved_check : checkSMachine interleaved_machine interleaved_proof = true := by decide +kernel
theorem interleaved_laws : ∀ ρ M, SReach interleaved_machine ρ M → ∀ e ∈ interleaved_proof, e.Holds ρ M :=
  smachine_sound interleaved_machine interleaved_proof interleaved_check
namespace interleaved
abbrev «cap» : Nat := 0
abbrev «a_n» : Nat := 3
abbrev «b_n» : Nat := 4
/-- a.n <= cap -/
theorem law0 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : SReach interleaved_machine ρ μ) : ρ «a_n» ≤ ρ «cap» := by
  have hl : interleaved_l0.Holds ρ μ := interleaved_laws ρ μ h interleaved_e0 (by simp [interleaved_proof])
  exact (evalC_iff ρ μ interleaved_l0.holds).mp hl
/-- b.n <= cap -/
theorem law1 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : SReach interleaved_machine ρ μ) : ρ «b_n» ≤ ρ «cap» := by
  have hl : interleaved_l1.Holds ρ μ := interleaved_laws ρ μ h interleaved_e1 (by simp [interleaved_proof])
  exact (evalC_iff ρ μ interleaved_l1.holds).mp hl
end interleaved

-- Step law: an a turn leaves b's count
def interleaved_step0 : SKStep := ⟨⟨[.eq (.var 2) (.const 0)],
  .eq (.var 7) (.var 4),
  [[]],
  [(3, 6), (4, 7)],
  [],
  [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .term (.ite (.le (.add (.var 4) (.var 1)) (.var 0)) (.add (.var 4) (.var 1)) (.var 4)), .term (.ite (.eq (.var 2) (.const 0)) (.var 4) (.ite (.le (.add (.var 4) (.var 1)) (.var 0)) (.add (.var 4) (.var 1)) (.var 4)))], .split (sp [(2, 1)] 0)
  (.split (sp [(2, (-1))] 0)
  (.leafAt [((sp [] 1), .fact 5)] [.input 0] [] [])
  (.leafAt [((sp [] 1), .fact 3)] [.input 0] [] []))
  (.leafAt [((sp [(2, (-1))] 1), .atom 0), ((sp [(2, 1)] 0), .fact 4)] [.input 0, .input 1, .combine 1 0 1 1] [] []))⟩,
  [[]],
  [],
  [],
  [],
  [],
  [.and (.le (.var 0) (.const 10)) (.le (.var 0) (.const 10)), .le (.var 3) (.var 0), .le (.var 4) (.var 0), .or (.eq (.var 2) (.const 0)) (.eq (.var 2) (.const 1)), .eq (.var 2) (.const 0), .not (.eq (.ite (.eq (.var 2) (.const 0)) (.var 4) (.ite (.le (.add (.var 4) (.var 1)) (.var 0)) (.add (.var 4) (.var 1)) (.var 4))) (.var 4))],
  []⟩
theorem interleaved_step0_holds : SKStepHolds interleaved_machine interleaved_step0 :=
  skstep_sound interleaved_machine interleaved_proof interleaved_step0 interleaved_check (by decide +kernel)

-- Step law over 2 steps: two a turns leave b's count
def interleaved_step1 : SKStep := ⟨⟨[.eq (.var 2) (.const 0), .eq (.var 2) (.const 0)],
  .eq (.var 7) (.var 4),
  [[], [(1, 8), (2, 9)]],
  [(3, 6), (4, 7)],
  [],
  [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .term (.ite (.le (.add (.var 3) (.var 1)) (.var 0)) (.add (.var 3) (.var 1)) (.var 3)), .term (.ite (.eq (.var 2) (.const 1)) (.var 3) (.ite (.le (.add (.var 3) (.var 1)) (.var 0)) (.add (.var 3) (.var 1)) (.var 3))), .term (.ite (.le (.add (.var 4) (.var 1)) (.var 0)) (.add (.var 4) (.var 1)) (.var 4)), .term (.ite (.eq (.var 2) (.const 0)) (.var 4) (.ite (.le (.add (.var 4) (.var 1)) (.var 0)) (.add (.var 4) (.var 1)) (.var 4))), .term (.ite (.le (.add (.var 11) (.var 8)) (.var 0)) (.add (.var 11) (.var 8)) (.var 11)), .term (.ite (.eq (.var 9) (.const 0)) (.var 11) (.ite (.le (.add (.var 11) (.var 8)) (.var 0)) (.add (.var 11) (.var 8)) (.var 11)))], .split (sp [(9, 1)] 0)
  (.split (sp [(9, (-1))] 0)
  (.split (sp [(4, (-1)), (11, 1)] 0)
  (.split (sp [(4, 1), (11, (-1))] 0)
  (.leafAt [((sp [] 1), .fact 11)] [.input 0] [] [])
  (.split (sp [(2, 1)] 0)
  (.split (sp [(2, (-1))] 0)
  (.leafAt [((sp [(4, (-1)), (11, 1)] 1), .atom 2), ((sp [(4, 1), (11, (-1))] 0), .fact 6)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leafAt [((sp [] 1), .fact 3)] [.input 0] [] []))
  (.leafAt [((sp [(2, (-1))] 1), .atom 0), ((sp [(2, 1)] 0), .fact 4)] [.input 0, .input 1, .combine 1 0 1 1] [] [])))
  (.split (sp [(2, 1)] 0)
  (.split (sp [(2, (-1))] 0)
  (.leafAt [((sp [(4, 1), (11, (-1))] 1), .atom 2), ((sp [(4, (-1)), (11, 1)] 0), .fact 6)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leafAt [((sp [] 1), .fact 3)] [.input 0] [] []))
  (.leafAt [((sp [(2, (-1))] 1), .atom 0), ((sp [(2, 1)] 0), .fact 4)] [.input 0, .input 1, .combine 1 0 1 1] [] [])))
  (.leafAt [((sp [] 1), .fact 9)] [.input 0] [] []))
  (.leafAt [((sp [(9, (-1))] 1), .atom 0), ((sp [(9, 1)] 0), .fact 10)] [.input 0, .input 1, .combine 1 0 1 1] [] []))⟩,
  [[], []],
  [],
  [],
  [],
  [],
  [.and (.le (.var 0) (.const 10)) (.le (.var 0) (.const 10)), .le (.var 3) (.var 0), .le (.var 4) (.var 0), .or (.eq (.var 2) (.const 0)) (.eq (.var 2) (.const 1)), .eq (.var 2) (.const 0), .eq (.var 10) (.ite (.eq (.var 2) (.const 1)) (.var 3) (.ite (.le (.add (.var 3) (.var 1)) (.var 0)) (.add (.var 3) (.var 1)) (.var 3))), .eq (.var 11) (.ite (.eq (.var 2) (.const 0)) (.var 4) (.ite (.le (.add (.var 4) (.var 1)) (.var 0)) (.add (.var 4) (.var 1)) (.var 4))), .le (.var 10) (.var 0), .le (.var 11) (.var 0), .or (.eq (.var 9) (.const 0)) (.eq (.var 9) (.const 1)), .eq (.var 9) (.const 0), .not (.eq (.ite (.eq (.var 9) (.const 0)) (.var 11) (.ite (.le (.add (.var 11) (.var 8)) (.var 0)) (.add (.var 11) (.var 8)) (.var 11))) (.var 4))],
  [[(3, 10), (4, 11)]]⟩
theorem interleaved_step1_holds : SKStepHolds interleaved_machine interleaved_step1 :=
  skstep_sound interleaved_machine interleaved_proof interleaved_step1 interleaved_check (by decide +kernel)

-- meter, two-phase refines meter: used = used; pending <= most, with flags b_fits  (variables 0 cap, 1 most, 2 op, 3 amount, 4 a_used, 5 a_pending, 6 b_used, 7 #, 8 ?b_fits, 9 a_used', 10 a_pending', 11 b_used'; maps )
def twophase_machine : FMMachine := ⟨⟨[2, 3],
  [(4, .const 0), (5, .const 0), (6, .const 0)],
  [],
  [(5, .ite (.eq (.var 2) (.const 0)) (.min (.var 3) (.var 1)) (.ite (.eq (.var 2) (.const 1)) (.const 0) (.var 5))), (4, .ite (.and (.eq (.var 2) (.const 1)) (.le (.add (.var 4) (.var 5)) (.var 0))) (.add (.var 4) (.var 5)) (.var 4)), (6, .ite (.eq (.var 2) (.const 0)) (.var 6) (.ite (.eq (.var 8) (.const 1)) (.add (.var 6) (.var 5)) (.var 6)))],
  [],
  .le (.const 0) (.const 0),
  .lt (.var 2) (.const 2)⟩,
  [(8, .le (.add (.var 6) (.var 5)) (.var 0))]⟩
def twophase_l0 : MLaw := ⟨.eq (.var 4) (.var 6), none⟩
def twophase_e0 : MEntry := ⟨twophase_l0, 7, [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11], .leafAt [((sp [] 1), .fact 0)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .term (.ite (.and (.eq (.var 2) (.const 1)) (.le (.add (.var 4) (.var 5)) (.var 0))) (.add (.var 4) (.var 5)) (.var 4)), .term (.ite (.le (.add (.var 6) (.var 5)) (.var 0)) (.add (.var 6) (.var 5)) (.var 6)), .term (.ite (.eq (.var 2) (.const 0)) (.var 6) (.ite (.le (.add (.var 6) (.var 5)) (.var 0)) (.add (.var 6) (.var 5)) (.var 6)))], .split (sp [(2, 1)] (-1))
  (.split (sp [(2, (-1))] 1)
  (.split (sp [(0, (-1)), (4, 1), (5, 1)] 0)
  (.split (sp [(0, (-1)), (5, 1), (6, 1)] 0)
  (.split (sp [(4, 1), (6, (-1))] 0)
  (.leafAt [((sp [(4, (-1)), (6, 1)] 0), .fact 1), ((sp [(4, 1), (6, (-1))] 1), .fact 3)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(4, (-1)), (6, 1)] 1), .atom 0), ((sp [(4, 1), (6, (-1))] 0), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(0, (-1)), (4, 1), (5, 1)] 0), .atom 1), ((sp [(0, 1), (5, (-1)), (6, (-1))] 1), .atom 0), ((sp [(4, (-1)), (6, 1)] 0), .fact 1)] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 3 1 1 1] [] []))
  (.split (sp [(0, (-1)), (5, 1), (6, 1)] 0)
  (.leafAt [((sp [(0, 1), (4, (-1)), (5, (-1))] 1), .atom 1), ((sp [(0, (-1)), (5, 1), (6, 1)] 0), .atom 0), ((sp [(4, 1), (6, (-1))] 0), .fact 1)] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 1 3 1 1] [] [])
  (.split (sp [(4, 1), (6, (-1))] 0)
  (.leafAt [((sp [(4, (-1)), (6, 1)] 0), .fact 1), ((sp [(4, 1), (6, (-1))] 1), .fact 3)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(4, (-1)), (6, 1)] 1), .atom 0), ((sp [(4, 1), (6, (-1))] 0), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []))))
  (.split (sp [(2, (-1))] 0)
  (.split (sp [(4, 1), (6, (-1))] 0)
  (.leafAt [((sp [(4, (-1)), (6, 1)] 0), .fact 1), ((sp [(4, 1), (6, (-1))] 1), .fact 3)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(4, (-1)), (6, 1)] 1), .atom 0), ((sp [(4, 1), (6, (-1))] 0), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(2, 1)] 1), .atom 0), ((sp [(2, (-1))] 0), .nat 2)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))
  (.leafAt [((sp [(2, (-1))] 2), .atom 0), ((sp [(2, 1)] (-1)), .fact 0)] [.input 0, .input 1, .combine 1 0 1 1] [] []))⟩
def twophase_l1 : MLaw := ⟨.le (.var 5) (.var 1), none⟩
def twophase_e1 : MEntry := ⟨twophase_l1, 7, [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11], .leafAt [((sp [(1, 1)] 1), .fact 0), ((sp [(1, (-1))] 0), .nat 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .term (.min (.var 3) (.var 1)), .term (.ite (.eq (.var 2) (.const 1)) (.const 0) (.var 5)), .term (.ite (.eq (.var 2) (.const 0)) (.min (.var 3) (.var 1)) (.ite (.eq (.var 2) (.const 1)) (.const 0) (.var 5)))], .split (sp [(2, 1)] 0)
  (.split (sp [(2, (-1))] 0)
  (.split (sp [(1, (-1)), (3, 1)] 0)
  (.leafAt [((sp [] 1), .fact 3)] [.input 0] [] [])
  (.leafAt [((sp [] 1), .fact 3)] [.input 0] [] []))
  (.leafAt [((sp [(2, 1)] 1), .atom 0), ((sp [(2, (-1))] 0), .nat 2)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split (sp [(2, 1)] (-1))
  (.leafAt [((sp [(1, 1)] 1), .fact 3), ((sp [(1, (-1))] 0), .nat 1)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leafAt [((sp [(2, (-1))] 2), .atom 0), ((sp [(2, 1)] (-1)), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩
def twophase_proof : List MEntry := [twophase_e0, twophase_e1]
theorem twophase_check : checkFMMachine twophase_machine twophase_proof = true := by decide +kernel
theorem twophase_laws : ∀ ρ M, FMReach twophase_machine ρ M → ∀ e ∈ twophase_proof, e.law.Holds ρ M :=
  fmmachine_sound twophase_machine twophase_proof twophase_check
namespace twophase
abbrev «most» : Nat := 1
abbrev «a_used» : Nat := 4
abbrev «a_pending» : Nat := 5
abbrev «b_used» : Nat := 6
/-- used = used -/
theorem law0 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach twophase_machine ρ μ) : ρ «a_used» = ρ «b_used» := by
  have hl : twophase_l0.Holds ρ μ := twophase_laws ρ μ h twophase_e0 (by simp [twophase_proof])
  exact (evalC_iff ρ μ twophase_l0.holds).mp hl
/-- pending <= most -/
theorem law1 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach twophase_machine ρ μ) : ρ «a_pending» ≤ ρ «most» := by
  have hl : twophase_l1.Holds ρ μ := twophase_laws ρ μ h twophase_e1 (by simp [twophase_proof])
  exact (evalC_iff ρ μ twophase_l1.holds).mp hl
end twophase

-- Step law: meter allows the request it is sent
def twophase_step0 : StepLaw := ⟨.le (.const 0) (.const 0),
  .or (.eq (.var 2) (.const 0)) (.le (.var 5) (.var 1)),
  [(4, 9), (5, 10), (6, 11)],
  [],
  [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11], .leafAt [((sp [(1, (-1)), (5, 1)] 0), .fact 1), ((sp [(1, 1), (5, (-1))] 1), .fact 3)] [.input 0, .input 1, .combine 0 1 1 1] [] [])⟩
theorem twophase_step0_holds : StepLawHolds twophase_machine twophase_step0 :=
  steplaw_sound twophase_machine twophase_proof twophase_step0 twophase_check (by decide +kernel)

-- escrow: a release closes it, with flags releasing, refunding  (variables 0 op, 1 amount, 2 held, 3 closed, 4 refunded, 5 released, 6 #, 7 ?releasing, 8 ?refunding, 9 held', 10 closed', 11 refunded', 12 released'; maps )
def escrow_machine : FMMachine := ⟨⟨[0, 1],
  [(2, .const 0), (3, .const 0), (4, .const 0), (5, .const 0)],
  [],
  [(2, .ite (.and (.eq (.var 0) (.const 0)) (.eq (.var 3) (.const 0))) (.add (.var 2) (.var 1)) (.ite (.or (.eq (.var 7) (.const 1)) (.eq (.var 8) (.const 1))) (.const 0) (.var 2))), (3, .ite (.eq (.var 7) (.const 1)) (.const 1) (.var 3)), (4, .ite (.eq (.var 8) (.const 1)) (.add (.var 4) (.var 2)) (.var 4)), (5, .ite (.eq (.var 7) (.const 1)) (.const 1) (.var 5))],
  [],
  .le (.const 0) (.const 0),
  .lt (.var 0) (.const 3)⟩,
  [(7, .and (.eq (.var 0) (.const 1)) (.and (.eq (.var 3) (.const 0)) (.lt (.const 0) (.var 2)))), (8, .and (.eq (.var 0) (.const 2)) (.and (.lt (.const 0) (.var 2)) (.eq (.var 3) (.const 0))))]⟩
def escrow_l0 : MLaw := ⟨.le (.var 5) (.var 3), none⟩
def escrow_e0 : MEntry := ⟨escrow_l0, 6, [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12], .leafAt [((sp [] 1), .fact 0)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .term (.ite (.and (.eq (.var 0) (.const 1)) (.and (.eq (.var 3) (.const 0)) (.lt (.const 0) (.var 2)))) (.const 1) (.var 5)), .term (.ite (.and (.eq (.var 0) (.const 1)) (.and (.eq (.var 3) (.const 0)) (.lt (.const 0) (.var 2)))) (.const 1) (.var 3))], .split (sp [(0, 1)] (-1))
  (.split (sp [(0, (-1))] 1)
  (.split (sp [(3, 1)] 0)
  (.split (sp [(3, (-1))] 0)
  (.split (sp [(2, (-1))] 1)
  (.leafAt [((sp [] 1), .fact 2)] [.input 0] [] [])
  (.leafAt [((sp [(3, 1)] 0), .atom 2), ((sp [(3, (-1)), (5, 1)] 0), .fact 1), ((sp [(3, 1), (5, (-1))] 1), .fact 2), ((sp [(3, (-1))] 0), .nat 3)] [.input 0, .input 1, .input 2, .input 3, .combine 1 0 1 1, .combine 2 3 1 1, .combine 5 4 1 1] [] []))
  (.leafAt [((sp [(3, 1)] 1), .atom 0), ((sp [(3, (-1))] 0), .nat 3)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(3, (-1)), (5, 1)] 0), .fact 1), ((sp [(3, 1), (5, (-1))] 1), .fact 2)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(3, (-1)), (5, 1)] 0), .fact 1), ((sp [(3, 1), (5, (-1))] 1), .fact 2)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(3, (-1)), (5, 1)] 0), .fact 1), ((sp [(3, 1), (5, (-1))] 1), .fact 2)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def escrow_proof : List MEntry := [escrow_e0]
theorem escrow_check : checkFMMachine escrow_machine escrow_proof = true := by decide +kernel
theorem escrow_laws : ∀ ρ M, FMReach escrow_machine ρ M → ∀ e ∈ escrow_proof, e.law.Holds ρ M :=
  fmmachine_sound escrow_machine escrow_proof escrow_check
namespace escrow
abbrev «closed» : Nat := 3
abbrev «released» : Nat := 5
/-- a release closes it -/
theorem law0 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach escrow_machine ρ μ) : ρ «released» ≤ ρ «closed» := by
  have hl : escrow_l0.Holds ρ μ := escrow_laws ρ μ h escrow_e0 (by simp [escrow_proof])
  exact (evalC_iff ρ μ escrow_l0.holds).mp hl
end escrow

-- Step law: no refund after a release
def escrow_step0 : StepLaw := ⟨.le (.const 0) (.const 0),
  .or (.eq (.var 5) (.const 0)) (.eq (.var 11) (.var 4)),
  [(2, 9), (3, 10), (4, 11), (5, 12)],
  [],
  [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .term (.ite (.and (.eq (.var 0) (.const 2)) (.and (.lt (.const 0) (.var 2)) (.eq (.var 3) (.const 0)))) (.add (.var 4) (.var 2)) (.var 4))], .split (sp [(5, 1)] 0)
  (.leafAt [((sp [(5, 1)] 1), .fact 2), ((sp [(5, (-1))] 0), .nat 5)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.split (sp [(3, 1)] 0)
  (.leafAt [((sp [(5, (-1))] 1), .atom 1), ((sp [(3, 1)] 0), .atom 0), ((sp [(3, (-1)), (5, 1)] 0), .fact 0)] [.input 0, .input 1, .input 2, .combine 2 1 1 1, .combine 0 3 1 1] [] [])
  (.leafAt [((sp [] 1), .fact 2)] [.input 0] [] [])))⟩
theorem escrow_step0_holds : StepLawHolds escrow_machine escrow_step0 :=
  steplaw_sound escrow_machine escrow_proof escrow_step0 escrow_check (by decide +kernel)

-- connection pool: in use <= pool size; in use + released = acquired; released <= acquired; every client holds <= its cap; in use = what the clients hold, with flags got, back  (variables 0 size, 1 perClient, 2 op, 3 client, 4 inUse, 5 acquired, 6 released, 7 heldTotal, 8 key$678, 9 key$678#, 10 #, 11 ?got, 12 ?back; maps 0 Held)
def pooltotal_machine : FMMachine := ⟨⟨[2, 3],
  [(4, .const 0), (5, .const 0), (6, .const 0), (7, .const 0)],
  [(0, 0)],
  [(4, .ite (.eq (.var 11) (.const 1)) (.add (.var 4) (.const 1)) (.ite (.eq (.var 12) (.const 1)) (.sub (.var 4) (.const 1)) (.var 4))), (5, .ite (.eq (.var 11) (.const 1)) (.add (.var 5) (.const 1)) (.var 5)), (6, .ite (.eq (.var 12) (.const 1)) (.add (.var 6) (.const 1)) (.var 6)), (7, .ite (.eq (.var 11) (.const 1)) (.add (.var 7) (.const 1)) (.ite (.eq (.var 12) (.const 1)) (.sub (.var 7) (.min (.const 1) (.get 0 (.var 3)))) (.var 7)))],
  [(0, .var 3, .ite (.eq (.var 11) (.const 1)) (.add (.get 0 (.var 3)) (.const 1)) (.ite (.eq (.var 12) (.const 1)) (.sub (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3))))],
  .le (.const 0) (.const 0),
  .lt (.var 2) (.const 2)⟩,
  [(11, .and (.eq (.var 2) (.const 0)) (.and (.lt (.var 4) (.var 0)) (.lt (.get 0 (.var 3)) (.var 1)))), (12, .and (.eq (.var 2) (.const 1)) (.and (.lt (.const 0) (.get 0 (.var 3))) (.lt (.const 0) (.var 4))))]⟩
def pooltotal_l0 : MLaw := ⟨.le (.var 4) (.var 0), none⟩
def pooltotal_e0 : MEntry := ⟨pooltotal_l0, 10, [(3, .var 3)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12], .leafAt [((sp [(0, 1)] 1), .fact 0), ((sp [(0, (-1))] 0), .nat 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .term (.sub (.var 4) (.const 1)), .term (.ite (.and (.eq (.var 2) (.const 1)) (.and (.lt (.const 0) (.get 0 (.var 3))) (.lt (.const 0) (.var 4)))) (.sub (.var 4) (.const 1)) (.var 4)), .term (.ite (.and (.eq (.var 2) (.const 0)) (.and (.lt (.var 4) (.var 0)) (.lt (.get 0 (.var 3)) (.var 1)))) (.add (.var 4) (.const 1)) (.ite (.and (.eq (.var 2) (.const 1)) (.and (.lt (.const 0) (.get 0 (.var 3))) (.lt (.const 0) (.var 4)))) (.sub (.var 4) (.const 1)) (.var 4))), .cell 0 (sp [(3, 1)] 0)], .split (sp [(2, 1)] 0)
  (.split (sp [(2, (-1))] 0)
  (.split (sp [(0, (-1)), (4, 1)] 1)
  (.split (sp [(1, (-1)), (16, 1)] 1)
  (.leafAt [((sp [] 1), .fact 6)] [.input 0] [] [])
  (.leafAt [((sp [(0, (-1)), (4, 1)] 1), .atom 1), ((sp [(4, 1), (5, (-1)), (6, 1)] 0), .fact 2), ((sp [(4, (-1)), (5, 1), (6, (-1))] 0), .fact 2), ((sp [(0, 1), (4, (-1))] 1), .fact 6)] [.input 0, .input 1, .input 2, .input 3, .combine 0 2 1 1, .combine 3 1 1 1, .combine 5 4 1 1] [] []))
  (.leafAt [((sp [(0, (-1)), (4, 1)] 0), .fact 1), ((sp [(0, 1), (4, (-1))] 1), .fact 6)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(2, 1)] 1), .atom 0), ((sp [(2, (-1))] 0), .nat 2)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split (sp [(2, 1)] (-1))
  (.split (sp [(16, (-1))] 1)
  (.split (sp [(4, (-1))] 1)
  (.leafAt [((sp [(0, (-1)), (4, 1)] 0), .fact 1), ((sp [(4, 1), (5, (-1)), (6, 1)] 0), .fact 2), ((sp [(4, (-1)), (5, 1), (6, (-1))] 0), .fact 2), ((sp [(0, 1), (4, (-1))] 2), .fact 6)] [.input 0, .input 1, .input 2, .input 3, .combine 0 2 1 1, .combine 3 1 1 1, .combine 4 5 1 1] [] [])
  (.leafAt [((sp [(4, 1)] 0), .atom 0), ((sp [(0, (-1)), (4, 1)] 0), .fact 1), ((sp [(0, 1), (4, (-1))] 1), .fact 6), ((sp [(4, (-1))] 0), .nat 4)] [.input 0, .input 1, .input 2, .input 3, .combine 1 3 1 1, .combine 2 0 1 1, .combine 5 4 1 1] [] []))
  (.leafAt [((sp [(0, (-1)), (4, 1)] 0), .fact 1), ((sp [(4, 1), (5, (-1)), (6, 1)] 0), .fact 2), ((sp [(4, (-1)), (5, 1), (6, (-1))] 0), .fact 2), ((sp [(0, 1), (4, (-1))] 1), .fact 6)] [.input 0, .input 1, .input 2, .input 3, .combine 0 2 1 1, .combine 3 1 1 1, .combine 5 4 1 1] [] []))
  (.leafAt [((sp [(2, (-1))] 2), .atom 0), ((sp [(2, 1)] (-1)), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩
def pooltotal_l1 : MLaw := ⟨.eq (.add (.var 4) (.var 6)) (.var 5), none⟩
def pooltotal_e1 : MEntry := ⟨pooltotal_l1, 10, [(3, .var 3)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12], .leafAt [((sp [] 1), .fact 0)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .term (.sub (.var 4) (.const 1)), .term (.ite (.and (.eq (.var 2) (.const 1)) (.and (.lt (.const 0) (.get 0 (.var 3))) (.lt (.const 0) (.var 4)))) (.sub (.var 4) (.const 1)) (.var 4)), .term (.ite (.and (.eq (.var 2) (.const 0)) (.and (.lt (.var 4) (.var 0)) (.lt (.get 0 (.var 3)) (.var 1)))) (.add (.var 4) (.const 1)) (.ite (.and (.eq (.var 2) (.const 1)) (.and (.lt (.const 0) (.get 0 (.var 3))) (.lt (.const 0) (.var 4)))) (.sub (.var 4) (.const 1)) (.var 4))), .term (.ite (.and (.eq (.var 2) (.const 1)) (.and (.lt (.const 0) (.get 0 (.var 3))) (.lt (.const 0) (.var 4)))) (.add (.var 6) (.const 1)) (.var 6)), .term (.ite (.and (.eq (.var 2) (.const 0)) (.and (.lt (.var 4) (.var 0)) (.lt (.get 0 (.var 3)) (.var 1)))) (.add (.var 5) (.const 1)) (.var 5)), .cell 0 (sp [(3, 1)] 0)], .split (sp [(2, 1)] 0)
  (.split (sp [(2, (-1))] 0)
  (.split (sp [(0, (-1)), (4, 1)] 1)
  (.split (sp [(1, (-1)), (18, 1)] 1)
  (.split (sp [(4, 1), (5, (-1)), (6, 1)] 0)
  (.leafAt [((sp [(4, (-1)), (5, 1), (6, (-1))] 0), .fact 2), ((sp [(4, 1), (5, (-1)), (6, 1)] 1), .fact 6)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(4, (-1)), (5, 1), (6, (-1))] 1), .atom 0), ((sp [(4, 1), (5, (-1)), (6, 1)] 0), .fact 2)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split (sp [(4, 1), (5, (-1)), (6, 1)] 0)
  (.leafAt [((sp [(4, (-1)), (5, 1), (6, (-1))] 0), .fact 2), ((sp [(4, 1), (5, (-1)), (6, 1)] 1), .fact 6)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(4, (-1)), (5, 1), (6, (-1))] 1), .atom 0), ((sp [(4, 1), (5, (-1)), (6, 1)] 0), .fact 2)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))
  (.split (sp [(4, 1), (5, (-1)), (6, 1)] 0)
  (.leafAt [((sp [(0, 1), (4, (-1))] 0), .atom 1), ((sp [(0, (-1)), (4, 1)] 0), .fact 1), ((sp [(4, (-1)), (5, 1), (6, (-1))] 0), .fact 2), ((sp [(4, 1), (5, (-1)), (6, 1)] 1), .fact 6)] [.input 0, .input 1, .input 2, .input 3, .combine 2 1 1 1, .combine 3 0 1 1, .combine 5 4 1 1] [] [])
  (.leafAt [((sp [(0, 1), (4, (-1))] 0), .atom 1), ((sp [(4, (-1)), (5, 1), (6, (-1))] 1), .atom 0), ((sp [(0, (-1)), (4, 1)] 0), .fact 1), ((sp [(4, 1), (5, (-1)), (6, 1)] 0), .fact 2)] [.input 0, .input 1, .input 2, .input 3, .combine 1 2 1 1, .combine 3 0 1 1, .combine 4 5 1 1] [] [])))
  (.leafAt [((sp [(2, 1)] 1), .atom 0), ((sp [(2, (-1))] 0), .nat 2)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split (sp [(2, 1)] (-1))
  (.split (sp [(18, (-1))] 1)
  (.split (sp [(4, (-1))] 1)
  (.split (sp [(4, 1), (5, (-1)), (6, 1)] 0)
  (.leafAt [((sp [(4, (-1)), (5, 1), (6, (-1))] 0), .fact 2), ((sp [(4, 1), (5, (-1)), (6, 1)] 1), .fact 6)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(4, (-1)), (5, 1), (6, (-1))] 1), .atom 0), ((sp [(4, 1), (5, (-1)), (6, 1)] 0), .fact 2)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split (sp [(4, 1), (5, (-1)), (6, 1)] 0)
  (.leafAt [((sp [(4, 1)] 0), .atom 1), ((sp [(4, (-1)), (5, 1), (6, (-1))] 0), .fact 2), ((sp [(4, 1), (5, (-1)), (6, 1)] 1), .fact 6), ((sp [(4, (-1))] 0), .nat 4)] [.input 0, .input 1, .input 2, .input 3, .combine 1 0 1 1, .combine 2 3 1 1, .combine 5 4 1 1] [] [])
  (.leafAt [((sp [(4, 1)] 0), .atom 1), ((sp [(4, (-1)), (5, 1), (6, (-1))] 1), .atom 0), ((sp [(4, 1), (5, (-1)), (6, 1)] 0), .fact 2), ((sp [(4, (-1))] 0), .nat 4)] [.input 0, .input 1, .input 2, .input 3, .combine 1 0 1 1, .combine 2 3 1 1, .combine 4 5 1 1] [] [])))
  (.split (sp [(4, 1), (5, (-1)), (6, 1)] 0)
  (.leafAt [((sp [(4, (-1)), (5, 1), (6, (-1))] 0), .fact 2), ((sp [(4, 1), (5, (-1)), (6, 1)] 1), .fact 6)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(4, (-1)), (5, 1), (6, (-1))] 1), .atom 0), ((sp [(4, 1), (5, (-1)), (6, 1)] 0), .fact 2)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))
  (.leafAt [((sp [(2, (-1))] 2), .atom 0), ((sp [(2, 1)] (-1)), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩
def pooltotal_l2 : MLaw := ⟨.le (.var 6) (.var 5), none⟩
def pooltotal_e2 : MEntry := ⟨pooltotal_l2, 10, [(3, .var 3)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12], .leafAt [((sp [] 1), .fact 0)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .term (.ite (.and (.eq (.var 2) (.const 1)) (.and (.lt (.const 0) (.get 0 (.var 3))) (.lt (.const 0) (.var 4)))) (.add (.var 6) (.const 1)) (.var 6)), .term (.ite (.and (.eq (.var 2) (.const 0)) (.and (.lt (.var 4) (.var 0)) (.lt (.get 0 (.var 3)) (.var 1)))) (.add (.var 5) (.const 1)) (.var 5)), .cell 0 (sp [(3, 1)] 0)], .split (sp [(2, 1)] (-1))
  (.split (sp [(2, (-1))] 1)
  (.split (sp [(15, (-1))] 1)
  (.split (sp [(4, (-1))] 1)
  (.leafAt [((sp [(4, (-1))] 1), .atom 0), ((sp [(4, 1), (5, (-1)), (6, 1)] 0), .fact 2), ((sp [(5, 1), (6, (-1))] 0), .fact 6)] [.input 0, .input 1, .input 2, .combine 0 1 1 1, .combine 3 2 1 1] [] [])
  (.leafAt [((sp [(4, 1), (5, (-1)), (6, 1)] 0), .fact 2), ((sp [(5, 1), (6, (-1))] 1), .fact 6), ((sp [(4, (-1))] 0), .nat 4)] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 1 3 1 1] [] []))
  (.leafAt [((sp [(5, (-1)), (6, 1)] 0), .fact 3), ((sp [(5, 1), (6, (-1))] 1), .fact 6)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split (sp [(2, (-1))] 0)
  (.split (sp [(0, (-1)), (4, 1)] 1)
  (.split (sp [(1, (-1)), (15, 1)] 1)
  (.leafAt [((sp [(5, (-1)), (6, 1)] 0), .fact 3), ((sp [(5, 1), (6, (-1))] 2), .fact 6)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leafAt [((sp [(5, (-1)), (6, 1)] 0), .fact 3), ((sp [(5, 1), (6, (-1))] 1), .fact 6)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(0, 1), (4, (-1))] 0), .atom 0), ((sp [(0, (-1)), (4, 1)] 0), .fact 1), ((sp [(4, 1), (5, (-1)), (6, 1)] 0), .fact 2), ((sp [(4, (-1)), (5, 1), (6, (-1))] 0), .fact 2), ((sp [(5, (-1)), (6, 1)] 0), .fact 3), ((sp [(5, 1), (6, (-1))] 1), .fact 6)] [.input 0, .input 1, .input 2, .input 3, .input 4, .input 5, .combine 2 0 1 1, .combine 3 1 1 1, .combine 4 7 1 1, .combine 5 6 1 1, .combine 9 8 1 1] [] []))
  (.leafAt [((sp [(2, 1)] 1), .atom 0), ((sp [(2, (-1))] 0), .nat 2)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))
  (.leafAt [((sp [(2, (-1))] 2), .atom 0), ((sp [(2, 1)] (-1)), .fact 0)] [.input 0, .input 1, .combine 1 0 1 1] [] []))⟩
def pooltotal_l3 : MLaw := ⟨.le (.get 0 (.var 8)) (.var 1), some 8⟩
def pooltotal_e3 : MEntry := ⟨pooltotal_l3, 9, [(3, .var 3), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12], .leafAt [((sp [(1, 1)] 1), .fact 0), ((sp [(1, (-1))] 0), .nat 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .term (.sub (.get 0 (.var 3)) (.const 1)), .term (.ite (.and (.eq (.var 2) (.const 1)) (.and (.lt (.const 0) (.get 0 (.var 3))) (.lt (.const 0) (.var 4)))) (.sub (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3))), .term (.ite (.and (.eq (.var 2) (.const 0)) (.and (.lt (.var 4) (.var 0)) (.lt (.get 0 (.var 3)) (.var 1)))) (.add (.get 0 (.var 3)) (.const 1)) (.ite (.and (.eq (.var 2) (.const 1)) (.and (.lt (.const 0) (.get 0 (.var 3))) (.lt (.const 0) (.var 4)))) (.sub (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3)))), .term (.ite (.eq (.var 9) (.var 3)) (.ite (.and (.eq (.var 2) (.const 0)) (.and (.lt (.var 4) (.var 0)) (.lt (.get 0 (.var 3)) (.var 1)))) (.add (.get 0 (.var 3)) (.const 1)) (.ite (.and (.eq (.var 2) (.const 1)) (.and (.lt (.const 0) (.get 0 (.var 3))) (.lt (.const 0) (.var 4)))) (.sub (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3)))) (.get 0 (.var 9))), .cell 0 (sp [(3, 1)] 0), .cell 0 (sp [(9, 1)] 0)], .split (sp [(3, (-1)), (9, 1)] 0)
  (.split (sp [(3, 1), (9, (-1))] 0)
  (.split (sp [(2, 1)] 0)
  (.split (sp [(2, (-1))] 0)
  (.split (sp [(0, (-1)), (4, 1)] 1)
  (.split (sp [(1, (-1)), (17, 1)] 1)
  (.leafAt [((sp [] 1), .fact 7)] [.input 0] [(17, 18)] [])
  (.leafAt [((sp [(1, (-1)), (17, 1)] 0), .fact 4), ((sp [(1, 1), (17, (-1))] 1), .fact 7)] [.input 0, .input 1, .combine 1 0 1 1] [(17, 18)] []))
  (.leafAt [((sp [(1, (-1)), (17, 1)] 0), .fact 4), ((sp [(1, 1), (17, (-1))] 1), .fact 7), ((sp [(17, 1), (18, (-1))] 0), .eq 0), ((sp [(17, (-1)), (18, 1)] 0), .eq 0)] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(17, 18)] []))
  (.leafAt [((sp [(2, 1)] 1), .atom 0), ((sp [(2, (-1))] 0), .nat 2)] [.input 0, .input 1, .combine 0 1 1 1] [(17, 18)] []))
  (.split (sp [(2, 1)] (-1))
  (.split (sp [(17, (-1))] 1)
  (.split (sp [(4, (-1))] 1)
  (.leafAt [((sp [(1, (-1)), (17, 1)] 0), .fact 4), ((sp [(1, 1), (17, (-1))] 2), .fact 7), ((sp [(17, 1), (18, (-1))] 0), .eq 0), ((sp [(17, (-1)), (18, 1)] 0), .eq 0)] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 4 5 1 1] [(17, 18)] [])
  (.leafAt [((sp [(1, (-1)), (17, 1)] 0), .fact 4), ((sp [(1, 1), (17, (-1))] 1), .fact 7), ((sp [(17, 1), (18, (-1))] 0), .eq 0), ((sp [(17, (-1)), (18, 1)] 0), .eq 0)] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 4 5 1 1] [(17, 18)] []))
  (.leafAt [((sp [(17, 1)] 0), .atom 0), ((sp [(1, (-1)), (17, 1)] 0), .fact 4), ((sp [(1, 1), (17, (-1))] 1), .fact 7), ((sp [(17, (-1))] 0), .nat 17)] [.input 0, .input 1, .input 2, .input 3, .combine 1 3 1 1, .combine 2 0 1 1, .combine 5 4 1 1] [(17, 18)] []))
  (.leafAt [((sp [(2, (-1))] 2), .atom 0), ((sp [(2, 1)] (-1)), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(17, 18)] [])))
  (.leafAt [((sp [(1, (-1)), (18, 1)] 0), .fact 5), ((sp [(1, 1), (18, (-1))] 1), .fact 7)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(1, (-1)), (18, 1)] 0), .fact 5), ((sp [(1, 1), (18, (-1))] 1), .fact 7)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def pooltotal_l4 : MLaw := ⟨.eq (.var 4) (.var 7), none⟩
def pooltotal_e4 : MEntry := ⟨pooltotal_l4, 10, [(3, .var 3)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12], .leafAt [((sp [] 1), .fact 0)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .term (.sub (.var 4) (.const 1)), .term (.ite (.and (.eq (.var 2) (.const 1)) (.and (.lt (.const 0) (.get 0 (.var 3))) (.lt (.const 0) (.var 4)))) (.sub (.var 4) (.const 1)) (.var 4)), .term (.ite (.and (.eq (.var 2) (.const 0)) (.and (.lt (.var 4) (.var 0)) (.lt (.get 0 (.var 3)) (.var 1)))) (.add (.var 4) (.const 1)) (.ite (.and (.eq (.var 2) (.const 1)) (.and (.lt (.const 0) (.get 0 (.var 3))) (.lt (.const 0) (.var 4)))) (.sub (.var 4) (.const 1)) (.var 4))), .term (.min (.const 1) (.get 0 (.var 3))), .term (.sub (.var 7) (.min (.const 1) (.get 0 (.var 3)))), .term (.ite (.and (.eq (.var 2) (.const 1)) (.and (.lt (.const 0) (.get 0 (.var 3))) (.lt (.const 0) (.var 4)))) (.sub (.var 7) (.min (.const 1) (.get 0 (.var 3)))) (.var 7)), .term (.ite (.and (.eq (.var 2) (.const 0)) (.and (.lt (.var 4) (.var 0)) (.lt (.get 0 (.var 3)) (.var 1)))) (.add (.var 7) (.const 1)) (.ite (.and (.eq (.var 2) (.const 1)) (.and (.lt (.const 0) (.get 0 (.var 3))) (.lt (.const 0) (.var 4)))) (.sub (.var 7) (.min (.const 1) (.get 0 (.var 3)))) (.var 7))), .cell 0 (sp [(3, 1)] 0)], .split (sp [(2, 1)] 0)
  (.split (sp [(2, (-1))] 0)
  (.split (sp [(0, (-1)), (4, 1)] 1)
  (.split (sp [(1, (-1)), (20, 1)] 1)
  (.split (sp [(4, 1), (7, (-1))] 0)
  (.leafAt [((sp [(4, (-1)), (7, 1)] 0), .fact 5), ((sp [(4, 1), (7, (-1))] 1), .fact 6)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(4, (-1)), (7, 1)] 1), .atom 0), ((sp [(4, 1), (5, (-1)), (6, 1)] 0), .fact 2), ((sp [(4, (-1)), (5, 1), (6, (-1))] 0), .fact 2), ((sp [(4, 1), (7, (-1))] 0), .fact 5)] [.input 0, .input 1, .input 2, .input 3, .combine 0 1 1 1, .combine 3 2 1 1, .combine 4 5 1 1] [] []))
  (.split (sp [(4, 1), (7, (-1))] 0)
  (.leafAt [((sp [(4, (-1)), (7, 1)] 0), .fact 5), ((sp [(4, 1), (7, (-1))] 1), .fact 6)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(4, (-1)), (7, 1)] 1), .atom 0), ((sp [(4, 1), (5, (-1)), (6, 1)] 0), .fact 2), ((sp [(4, (-1)), (5, 1), (6, (-1))] 0), .fact 2), ((sp [(4, 1), (7, (-1))] 0), .fact 5)] [.input 0, .input 1, .input 2, .input 3, .combine 0 1 1 1, .combine 3 2 1 1, .combine 4 5 1 1] [] [])))
  (.split (sp [(4, 1), (7, (-1))] 0)
  (.leafAt [((sp [(0, 1), (4, (-1))] 0), .atom 1), ((sp [(0, (-1)), (4, 1)] 0), .fact 1), ((sp [(4, (-1)), (7, 1)] 0), .fact 5), ((sp [(4, 1), (7, (-1))] 1), .fact 6)] [.input 0, .input 1, .input 2, .input 3, .combine 2 1 1 1, .combine 3 0 1 1, .combine 5 4 1 1] [] [])
  (.leafAt [((sp [(0, 1), (4, (-1))] 0), .atom 1), ((sp [(4, (-1)), (7, 1)] 1), .atom 0), ((sp [(0, (-1)), (4, 1)] 0), .fact 1), ((sp [(4, 1), (7, (-1))] 0), .fact 5)] [.input 0, .input 1, .input 2, .input 3, .combine 1 2 1 1, .combine 3 0 1 1, .combine 4 5 1 1] [] [])))
  (.leafAt [((sp [(2, 1)] 1), .atom 0), ((sp [(2, (-1))] 0), .nat 2)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split (sp [(2, 1)] (-1))
  (.split (sp [(20, (-1))] 1)
  (.split (sp [(4, (-1))] 1)
  (.split (sp [(7, (-1))] 1)
  (.split (sp [(4, 1), (7, (-1))] 0)
  (.leafAt [((sp [(4, (-1)), (7, 1)] 0), .fact 5), ((sp [(4, 1), (7, (-1))] 1), .fact 6)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(4, (-1)), (7, 1)] 1), .atom 0), ((sp [(4, 1), (5, (-1)), (6, 1)] 0), .fact 2), ((sp [(4, (-1)), (5, 1), (6, (-1))] 0), .fact 2), ((sp [(4, 1), (7, (-1))] 0), .fact 5)] [.input 0, .input 1, .input 2, .input 3, .combine 0 1 1 1, .combine 3 2 1 1, .combine 4 5 1 1] [] []))
  (.leafAt [((sp [(4, (-1))] 1), .atom 1), ((sp [(7, 1)] 0), .atom 0), ((sp [(4, 1), (5, (-1)), (6, 1)] 0), .fact 2), ((sp [(4, (-1)), (5, 1), (6, (-1))] 0), .fact 2), ((sp [(4, 1), (7, (-1))] 0), .fact 5)] [.input 0, .input 1, .input 2, .input 3, .input 4, .combine 4 1 1 1, .combine 0 2 1 1, .combine 5 3 1 1, .combine 6 7 1 1] [] []))
  (.split (sp [(4, 1), (7, (-1))] 0)
  (.leafAt [((sp [(4, 1)] 0), .atom 1), ((sp [(4, (-1)), (7, 1)] 0), .fact 5), ((sp [(4, 1), (7, (-1))] 1), .fact 6), ((sp [(4, (-1))] 0), .nat 4)] [.input 0, .input 1, .input 2, .input 3, .combine 1 0 1 1, .combine 2 3 1 1, .combine 5 4 1 1] [] [])
  (.leafAt [((sp [(4, 1)] 0), .atom 1), ((sp [(4, (-1)), (7, 1)] 1), .atom 0), ((sp [(4, 1), (7, (-1))] 0), .fact 5), ((sp [(4, (-1))] 0), .nat 4)] [.input 0, .input 1, .input 2, .input 3, .combine 1 0 1 1, .combine 2 3 1 1, .combine 4 5 1 1] [] [])))
  (.split (sp [(4, 1), (7, (-1))] 0)
  (.leafAt [((sp [(4, (-1)), (7, 1)] 0), .fact 5), ((sp [(4, 1), (7, (-1))] 1), .fact 6)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(4, (-1)), (7, 1)] 1), .atom 0), ((sp [(4, 1), (5, (-1)), (6, 1)] 0), .fact 2), ((sp [(4, (-1)), (5, 1), (6, (-1))] 0), .fact 2), ((sp [(4, 1), (7, (-1))] 0), .fact 5)] [.input 0, .input 1, .input 2, .input 3, .combine 0 1 1 1, .combine 3 2 1 1, .combine 4 5 1 1] [] [])))
  (.leafAt [((sp [(2, (-1))] 2), .atom 0), ((sp [(2, 1)] (-1)), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩
def pooltotal_proof : List MEntry := [pooltotal_e0, pooltotal_e1, pooltotal_e2, pooltotal_e3, pooltotal_e4]
theorem pooltotal_check : checkFMMachine pooltotal_machine pooltotal_proof = true := by decide +kernel
theorem pooltotal_laws : ∀ ρ M, FMReach pooltotal_machine ρ M → ∀ e ∈ pooltotal_proof, e.law.Holds ρ M :=
  fmmachine_sound pooltotal_machine pooltotal_proof pooltotal_check
namespace pooltotal
abbrev «size» : Nat := 0
abbrev «perClient» : Nat := 1
abbrev «inUse» : Nat := 4
abbrev «acquired» : Nat := 5
abbrev «released» : Nat := 6
abbrev «heldTotal» : Nat := 7
abbrev «Held» : Nat := 0
/-- in use <= pool size -/
theorem law0 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach pooltotal_machine ρ μ) : ρ «inUse» ≤ ρ «size» := by
  have hl : pooltotal_l0.Holds ρ μ := pooltotal_laws ρ μ h pooltotal_e0 (by simp [pooltotal_proof])
  exact (evalC_iff ρ μ pooltotal_l0.holds).mp hl
/-- in use + released = acquired -/
theorem law1 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach pooltotal_machine ρ μ) : (ρ «inUse» + ρ «released») = ρ «acquired» := by
  have hl : pooltotal_l1.Holds ρ μ := pooltotal_laws ρ μ h pooltotal_e1 (by simp [pooltotal_proof])
  exact (evalC_iff ρ μ pooltotal_l1.holds).mp hl
/-- released <= acquired -/
theorem law2 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach pooltotal_machine ρ μ) : ρ «released» ≤ ρ «acquired» := by
  have hl : pooltotal_l2.Holds ρ μ := pooltotal_laws ρ μ h pooltotal_e2 (by simp [pooltotal_proof])
  exact (evalC_iff ρ μ pooltotal_l2.holds).mp hl
/-- every client holds <= its cap -/
theorem law3 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach pooltotal_machine ρ μ) : ∀ k : Nat, (μ «Held» (k)) ≤ ρ «perClient» := by
  have hl : pooltotal_l3.Holds ρ μ := pooltotal_laws ρ μ h pooltotal_e3 (by simp [pooltotal_proof])
  exact fun k => (evalC_iff (upd ρ 8 k) μ pooltotal_l3.holds).mp (hl k)
/-- in use = what the clients hold -/
theorem law4 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach pooltotal_machine ρ μ) : ρ «inUse» = ρ «heldTotal» := by
  have hl : pooltotal_l4.Holds ρ μ := pooltotal_laws ρ μ h pooltotal_e4 (by simp [pooltotal_proof])
  exact (evalC_iff ρ μ pooltotal_l4.holds).mp hl
end pooltotal

-- TAMPERED: the two-turn law's proof offered without its whens (b may move on its own turns). Lean computes the check to false.
example : checkSKStep interleaved_machine interleaved_proof { interleaved_step1 with k := { interleaved_step1.k with whens := [.le (.const 0) (.const 0), .le (.const 0) (.const 0)] } } = false := by decide +kernel

-- in-flight requests: in-flight loss: s <= b + 3 × 50; s + 50p <= b + 150  (variables 0 b, 1 t, 2 done, 3 s, 4 p, 5 #, 6 s', 7 p'; maps )
def pflight_machine : FMMachine := ⟨⟨[1, 2],
  [(3, .const 0), (4, .const 0)],
  [],
  [(3, .ite (.and (.eq (.var 2) (.const 1)) (.lt (.const 0) (.var 4))) (.add (.var 3) (.min (.var 1) (.const 50))) (.var 3)), (4, .ite (.eq (.var 2) (.const 1)) (.ite (.lt (.const 0) (.var 4)) (.sub (.var 4) (.const 1)) (.var 4)) (.ite (.and (.lt (.var 3) (.var 0)) (.lt (.var 4) (.const 3))) (.add (.var 4) (.const 1)) (.var 4)))],
  [],
  .le (.const 0) (.const 0),
  .or (.eq (.var 2) (.const 0)) (.eq (.var 2) (.const 1))⟩,
  []⟩
def pflight_l0 : MLaw := ⟨.le (.var 3) (.add (.var 0) (.const 150)), none⟩
def pflight_e0 : MEntry := ⟨pflight_l0, 5, [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .leafAt [((sp [(0, 1)] 151), .fact 0), ((sp [(0, (-1))] 0), .nat 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .term (.min (.var 1) (.const 50)), .term (.ite (.and (.eq (.var 2) (.const 1)) (.lt (.const 0) (.var 4))) (.add (.var 3) (.min (.var 1) (.const 50))) (.var 3))], .split (sp [(2, 1)] (-1))
  (.split (sp [(2, (-1))] 1)
  (.split (sp [(4, (-1))] 1)
  (.split (sp [(1, 1)] (-50))
  (.leafAt [((sp [(4, (-1))] 1), .atom 1), ((sp [(1, 1)] (-50)), .atom 0), ((sp [(0, (-1)), (3, 1), (4, 50)] (-150)), .fact 2), ((sp [(0, 1), (1, (-1)), (3, (-1))] 151), .fact 3)] [.input 0, .input 1, .input 2, .input 3, .combine 2 0 1 50, .combine 1 3 1 1, .combine 4 5 1 1] [] [])
  (.leafAt [((sp [(4, (-1))] 1), .atom 1), ((sp [(0, (-1)), (3, 1), (4, 50)] (-150)), .fact 2), ((sp [(0, 1), (3, (-1))] 101), .fact 3)] [.input 0, .input 1, .input 2, .combine 1 0 1 50, .combine 3 2 1 1] [] []))
  (.leafAt [((sp [(0, (-1)), (3, 1)] (-150)), .fact 1), ((sp [(0, 1), (3, (-1))] 151), .fact 3)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(0, (-1)), (3, 1)] (-150)), .fact 1), ((sp [(0, 1), (3, (-1))] 151), .fact 3)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(2, (-1))] 2), .atom 0), ((sp [(2, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def pflight_l1 : MLaw := ⟨.le (.add (.var 3) (.mul 50 (.var 4))) (.add (.var 0) (.const 150)), none⟩
def pflight_e1 : MEntry := ⟨pflight_l1, 5, [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .leafAt [((sp [(0, 1)] 151), .fact 0), ((sp [(0, (-1))] 0), .nat 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .term (.min (.var 1) (.const 50)), .term (.ite (.and (.eq (.var 2) (.const 1)) (.lt (.const 0) (.var 4))) (.add (.var 3) (.min (.var 1) (.const 50))) (.var 3)), .term (.ite (.and (.lt (.var 3) (.var 0)) (.lt (.var 4) (.const 3))) (.add (.var 4) (.const 1)) (.var 4)), .term (.sub (.var 4) (.const 1)), .term (.ite (.lt (.const 0) (.var 4)) (.sub (.var 4) (.const 1)) (.var 4)), .term (.ite (.eq (.var 2) (.const 1)) (.ite (.lt (.const 0) (.var 4)) (.sub (.var 4) (.const 1)) (.var 4)) (.ite (.and (.lt (.var 3) (.var 0)) (.lt (.var 4) (.const 3))) (.add (.var 4) (.const 1)) (.var 4)))], .split (sp [(2, 1)] (-1))
  (.split (sp [(2, (-1))] 1)
  (.split (sp [(4, (-1))] 1)
  (.split (sp [(1, 1)] (-50))
  (.leafAt [((sp [(1, 1)] (-50)), .atom 0), ((sp [(0, (-1)), (3, 1), (4, 50)] (-150)), .fact 2), ((sp [(0, 1), (1, (-1)), (3, (-1)), (4, (-50))] 201), .fact 3)] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 3 1 1 1] [] [])
  (.leafAt [((sp [(0, (-1)), (3, 1), (4, 50)] (-150)), .fact 2), ((sp [(0, 1), (3, (-1)), (4, (-50))] 151), .fact 3)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(4, 1)] 0), .atom 0), ((sp [(0, (-1)), (3, 1)] (-150)), .fact 1), ((sp [(0, 1), (3, (-1)), (4, (-50))] 151), .fact 3)] [.input 0, .input 1, .input 2, .combine 2 0 1 50, .combine 3 1 1 1] [] []))
  (.split (sp [(0, (-1)), (3, 1)] 1)
  (.split (sp [(4, 1)] (-2))
  (.leafAt [((sp [(0, (-1)), (3, 1)] 1), .atom 1), ((sp [(4, 1)] (-2)), .atom 0), ((sp [(0, 1), (3, (-1)), (4, (-50))] 101), .fact 3)] [.input 0, .input 1, .input 2, .combine 2 0 1 1, .cut 3 50 [(4, (-1))] 3, .combine 1 4 1 1] [] [])
  (.leafAt [((sp [(0, (-1)), (3, 1), (4, 50)] (-150)), .fact 2), ((sp [(0, 1), (3, (-1)), (4, (-50))] 151), .fact 3)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(0, (-1)), (3, 1), (4, 50)] (-150)), .fact 2), ((sp [(0, 1), (3, (-1)), (4, (-50))] 151), .fact 3)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))
  (.leafAt [((sp [(2, (-1))] 2), .atom 0), ((sp [(2, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def pflight_proof : List MEntry := [pflight_e0, pflight_e1]
theorem pflight_check : checkFMMachine pflight_machine pflight_proof = true := by decide +kernel
theorem pflight_laws : ∀ ρ M, FMReach pflight_machine ρ M → ∀ e ∈ pflight_proof, e.law.Holds ρ M :=
  fmmachine_sound pflight_machine pflight_proof pflight_check
namespace pflight
abbrev «b» : Nat := 0
abbrev «s» : Nat := 3
abbrev «p» : Nat := 4
/-- in-flight loss: s <= b + 3 × 50 -/
theorem law0 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach pflight_machine ρ μ) : ρ «s» ≤ (ρ «b» + 150) := by
  have hl : pflight_l0.Holds ρ μ := pflight_laws ρ μ h pflight_e0 (by simp [pflight_proof])
  exact (evalC_iff ρ μ pflight_l0.holds).mp hl
/-- s + 50p <= b + 150 -/
theorem law1 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach pflight_machine ρ μ) : (ρ «s» + (50 * ρ «p»)) ≤ (ρ «b» + 150) := by
  have hl : pflight_l1.Holds ρ μ := pflight_laws ρ μ h pflight_e1 (by simp [pflight_proof])
  exact (evalC_iff ρ μ pflight_l1.holds).mp hl
end pflight

-- Progress: in-flight: a request in flight can always complete
def flight_complete : Progress := ⟨.le (.const 1) (.var 4),
  .lt (.var 7) (.var 4),
  [(1, .const 0), (2, .const 1)],
  [(3, 6), (4, 7)],
  [],
  [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .leafAt [((sp [] 1), .fact 3)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .term (.ite (.and (.lt (.var 3) (.var 0)) (.lt (.var 4) (.const 3))) (.add (.var 4) (.const 1)) (.var 4)), .term (.sub (.var 4) (.const 1)), .term (.ite (.lt (.const 0) (.var 4)) (.sub (.var 4) (.const 1)) (.var 4)), .term (.ite (.eq (.const 1) (.const 1)) (.ite (.lt (.const 0) (.var 4)) (.sub (.var 4) (.const 1)) (.var 4)) (.ite (.and (.lt (.var 3) (.var 0)) (.lt (.var 4) (.const 3))) (.add (.var 4) (.const 1)) (.var 4)))], .split (sp [(4, (-1))] 1)
  (.leafAt [((sp [] 1), .fact 3)] [.input 0] [] [])
  (.leafAt [((sp [(4, 1)] 0), .atom 0), ((sp [(4, (-1))] 1), .fact 2)] [.input 0, .input 1, .combine 1 0 1 1] [] []))⟩
theorem flight_complete_holds : ProgressHolds pflight_machine flight_complete :=
  progress_sound pflight_machine pflight_proof flight_complete pflight_check (by decide +kernel)
-- TAMPERED: with none in flight, one completes (false): the proof above offered for it. Lean computes the check to false.
def flight_complete_tampered : Progress := ⟨.eq (.var 4) (.const 0),
  .lt (.var 7) (.var 4),
  [(1, .const 0), (2, .const 1)],
  [(3, 6), (4, 7)],
  [],
  [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .leafAt [((sp [] 1), .fact 3)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .term (.ite (.and (.lt (.var 3) (.var 0)) (.lt (.var 4) (.const 3))) (.add (.var 4) (.const 1)) (.var 4)), .term (.sub (.var 4) (.const 1)), .term (.ite (.lt (.const 0) (.var 4)) (.sub (.var 4) (.const 1)) (.var 4)), .term (.ite (.eq (.const 1) (.const 1)) (.ite (.lt (.const 0) (.var 4)) (.sub (.var 4) (.const 1)) (.var 4)) (.ite (.and (.lt (.var 3) (.var 0)) (.lt (.var 4) (.const 3))) (.add (.var 4) (.const 1)) (.var 4)))], .split (sp [(4, (-1))] 1)
  (.leafAt [((sp [] 1), .fact 3)] [.input 0] [] [])
  (.leafAt [((sp [(4, 1)] 0), .atom 0), ((sp [(4, (-1))] 1), .fact 2)] [.input 0, .input 1, .combine 1 0 1 1] [] []))⟩
example : checkProgress pflight_machine pflight_proof flight_complete_tampered = false := by decide +kernel

-- Progress: in-flight: under budget with room, one is admitted
def flight_admit : Progress := ⟨.and (.lt (.var 3) (.var 0)) (.lt (.var 4) (.const 3)),
  .eq (.var 7) (.add (.var 4) (.const 1)),
  [(1, .const 0), (2, .const 0)],
  [(3, 6), (4, 7)],
  [],
  [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .leafAt [((sp [] 1), .fact 3)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .term (.ite (.and (.lt (.var 3) (.var 0)) (.lt (.var 4) (.const 3))) (.add (.var 4) (.const 1)) (.var 4)), .term (.sub (.var 4) (.const 1)), .term (.ite (.lt (.const 0) (.var 4)) (.sub (.var 4) (.const 1)) (.var 4)), .term (.ite (.eq (.const 0) (.const 1)) (.ite (.lt (.const 0) (.var 4)) (.sub (.var 4) (.const 1)) (.var 4)) (.ite (.and (.lt (.var 3) (.var 0)) (.lt (.var 4) (.const 3))) (.add (.var 4) (.const 1)) (.var 4)))], .split (sp [(0, (-1)), (3, 1)] 1)
  (.split (sp [(4, 1)] (-2))
  (.leafAt [((sp [] 1), .fact 3)] [.input 0] [] [])
  (.leafAt [((sp [(4, (-1))] 3), .atom 0), ((sp [(4, 1)] (-2)), .fact 2)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(0, 1), (3, (-1))] 0), .atom 0), ((sp [(0, (-1)), (3, 1)] 1), .fact 2)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
theorem flight_admit_holds : ProgressHolds pflight_machine flight_admit :=
  progress_sound pflight_machine pflight_proof flight_admit pflight_check (by decide +kernel)

-- admit: once_per_account: every Acct count <= its cap; day_cap: every Day count <= its cap; hour_cap: every Hour count <= its cap; dom_cap: every Dom count <= its cap  (variables 0 d, 1 hr, 2 dm, 3 acct, 4 day, 5 hour, 6 dom, 7 ok, 8 k, 9 k#, 10 #, 11 A, 12 D, 13 H, 14 M; maps 0 Acct, 1 Day, 2 Hour, 3 Dom, 4 Acct', 5 Day', 6 Hour', 7 Dom')
def padmit_machine : FMMachine := ⟨⟨[3, 4, 5, 6, 7],
  [],
  [(0, 0), (1, 0), (2, 0), (3, 0)],
  [],
  [(0, .var 3, .ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3))), (1, .var 4, .ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 1 (.var 4)) (.const 1)) (.get 1 (.var 4))), (2, .var 5, .ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 2 (.var 5)) (.const 1)) (.get 2 (.var 5))), (3, .var 6, .ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 3 (.var 6)) (.const 1)) (.get 3 (.var 6)))],
  .le (.const 0) (.const 0),
  .or (.eq (.var 7) (.const 0)) (.eq (.var 7) (.const 1))⟩,
  []⟩
def padmit_l0 : MLaw := ⟨.le (.get 0 (.var 8)) (.const 1), some 8⟩
def padmit_e0 : MEntry := ⟨padmit_l0, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14], .leafAt [((sp [] 1), .fact 0)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .term (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3))), .term (.ite (.eq (.var 9) (.var 3)) (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3))) (.get 0 (.var 9))), .cell 0 (sp [(3, 1)] 0), .cell 1 (sp [(4, 1)] 0), .cell 2 (sp [(5, 1)] 0), .cell 3 (sp [(6, 1)] 0), .cell 0 (sp [(4, 1)] 0), .cell 0 (sp [(5, 1)] 0), .cell 0 (sp [(6, 1)] 0), .cell 0 (sp [(9, 1)] 0), .cell 1 (sp [(3, 1)] 0), .cell 1 (sp [(5, 1)] 0), .cell 1 (sp [(6, 1)] 0), .cell 1 (sp [(9, 1)] 0), .cell 2 (sp [(3, 1)] 0), .cell 2 (sp [(4, 1)] 0), .cell 2 (sp [(6, 1)] 0), .cell 2 (sp [(9, 1)] 0), .cell 3 (sp [(3, 1)] 0), .cell 3 (sp [(4, 1)] 0), .cell 3 (sp [(5, 1)] 0), .cell 3 (sp [(9, 1)] 0)], .split (sp [(3, (-1)), (9, 1)] 0)
  (.split (sp [(3, 1), (9, (-1))] 0)
  (.split (sp [(7, 1)] (-1))
  (.split (sp [(7, (-1))] 1)
  (.split (sp [(17, 1)] 0)
  (.split (sp [(0, (-1)), (18, 1)] 1)
  (.split (sp [(1, (-1)), (19, 1)] 1)
  (.split (sp [(2, (-1)), (20, 1)] 1)
  (.leafAt [((sp [] 1), .fact 21)] [.input 0] [(17, 24), (25, 28), (29, 32), (33, 36)] [])
  (.leafAt [((sp [(17, 1)] 0), .atom 3), ((sp [(17, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(17, 24), (25, 28), (29, 32), (33, 36)] []))
  (.leafAt [((sp [(17, 1)] 0), .atom 2), ((sp [(17, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(17, 24), (25, 28), (29, 32), (33, 36)] []))
  (.leafAt [((sp [(17, 1)] 0), .atom 1), ((sp [(17, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(17, 24), (25, 28), (29, 32), (33, 36)] []))
  (.leafAt [((sp [(17, 1)] (-1)), .fact 1), ((sp [(17, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(17, 24), (25, 28), (29, 32), (33, 36)] []))
  (.leafAt [((sp [(17, 1)] (-1)), .fact 1), ((sp [(17, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(17, 24), (25, 28), (29, 32), (33, 36)] []))
  (.leafAt [((sp [(7, (-1))] 2), .atom 0), ((sp [(7, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(17, 24), (25, 28), (29, 32), (33, 36)] []))
  (.leafAt [((sp [(24, 1)] (-1)), .fact 5), ((sp [(24, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(24, 1)] (-1)), .fact 5), ((sp [(24, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def padmit_l1 : MLaw := ⟨.le (.get 1 (.var 8)) (.var 0), some 8⟩
def padmit_e1 : MEntry := ⟨padmit_l1, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14], .leafAt [((sp [(0, 1)] 1), .fact 0), ((sp [(0, (-1))] 0), .nat 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .term (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 1 (.var 4)) (.const 1)) (.get 1 (.var 4))), .term (.ite (.eq (.var 9) (.var 4)) (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 1 (.var 4)) (.const 1)) (.get 1 (.var 4))) (.get 1 (.var 9))), .cell 0 (sp [(3, 1)] 0), .cell 1 (sp [(4, 1)] 0), .cell 2 (sp [(5, 1)] 0), .cell 3 (sp [(6, 1)] 0), .cell 0 (sp [(4, 1)] 0), .cell 0 (sp [(5, 1)] 0), .cell 0 (sp [(6, 1)] 0), .cell 0 (sp [(9, 1)] 0), .cell 1 (sp [(3, 1)] 0), .cell 1 (sp [(5, 1)] 0), .cell 1 (sp [(6, 1)] 0), .cell 1 (sp [(9, 1)] 0), .cell 2 (sp [(3, 1)] 0), .cell 2 (sp [(4, 1)] 0), .cell 2 (sp [(6, 1)] 0), .cell 2 (sp [(9, 1)] 0), .cell 3 (sp [(3, 1)] 0), .cell 3 (sp [(4, 1)] 0), .cell 3 (sp [(5, 1)] 0), .cell 3 (sp [(9, 1)] 0)], .split (sp [(4, (-1)), (9, 1)] 0)
  (.split (sp [(4, 1), (9, (-1))] 0)
  (.split (sp [(7, 1)] (-1))
  (.split (sp [(7, (-1))] 1)
  (.split (sp [(17, 1)] 0)
  (.split (sp [(0, (-1)), (18, 1)] 1)
  (.split (sp [(1, (-1)), (19, 1)] 1)
  (.split (sp [(2, (-1)), (20, 1)] 1)
  (.leafAt [((sp [] 1), .fact 21)] [.input 0] [(18, 28), (21, 24), (30, 32), (34, 36)] [])
  (.leafAt [((sp [(0, (-1)), (18, 1)] 1), .atom 2), ((sp [(0, 1), (18, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(18, 28), (21, 24), (30, 32), (34, 36)] []))
  (.leafAt [((sp [(0, (-1)), (18, 1)] 1), .atom 1), ((sp [(0, 1), (18, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(18, 28), (21, 24), (30, 32), (34, 36)] []))
  (.leafAt [((sp [(0, (-1)), (18, 1)] 0), .fact 7), ((sp [(0, 1), (18, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(18, 28), (21, 24), (30, 32), (34, 36)] []))
  (.leafAt [((sp [(0, (-1)), (18, 1)] 0), .fact 7), ((sp [(0, 1), (18, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(18, 28), (21, 24), (30, 32), (34, 36)] []))
  (.leafAt [((sp [(0, (-1)), (18, 1)] 0), .fact 7), ((sp [(0, 1), (18, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(18, 28), (21, 24), (30, 32), (34, 36)] []))
  (.leafAt [((sp [(7, (-1))] 2), .atom 0), ((sp [(7, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(18, 28), (21, 24), (30, 32), (34, 36)] []))
  (.leafAt [((sp [(0, (-1)), (28, 1)] 0), .fact 10), ((sp [(0, 1), (28, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(0, (-1)), (28, 1)] 0), .fact 10), ((sp [(0, 1), (28, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def padmit_l2 : MLaw := ⟨.le (.get 2 (.var 8)) (.var 1), some 8⟩
def padmit_e2 : MEntry := ⟨padmit_l2, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14], .leafAt [((sp [(1, 1)] 1), .fact 0), ((sp [(1, (-1))] 0), .nat 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .term (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 2 (.var 5)) (.const 1)) (.get 2 (.var 5))), .term (.ite (.eq (.var 9) (.var 5)) (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 2 (.var 5)) (.const 1)) (.get 2 (.var 5))) (.get 2 (.var 9))), .cell 0 (sp [(3, 1)] 0), .cell 1 (sp [(4, 1)] 0), .cell 2 (sp [(5, 1)] 0), .cell 3 (sp [(6, 1)] 0), .cell 0 (sp [(4, 1)] 0), .cell 0 (sp [(5, 1)] 0), .cell 0 (sp [(6, 1)] 0), .cell 0 (sp [(9, 1)] 0), .cell 1 (sp [(3, 1)] 0), .cell 1 (sp [(5, 1)] 0), .cell 1 (sp [(6, 1)] 0), .cell 1 (sp [(9, 1)] 0), .cell 2 (sp [(3, 1)] 0), .cell 2 (sp [(4, 1)] 0), .cell 2 (sp [(6, 1)] 0), .cell 2 (sp [(9, 1)] 0), .cell 3 (sp [(3, 1)] 0), .cell 3 (sp [(4, 1)] 0), .cell 3 (sp [(5, 1)] 0), .cell 3 (sp [(9, 1)] 0)], .split (sp [(5, (-1)), (9, 1)] 0)
  (.split (sp [(5, 1), (9, (-1))] 0)
  (.split (sp [(7, 1)] (-1))
  (.split (sp [(7, (-1))] 1)
  (.split (sp [(17, 1)] 0)
  (.split (sp [(0, (-1)), (18, 1)] 1)
  (.split (sp [(1, (-1)), (19, 1)] 1)
  (.split (sp [(2, (-1)), (20, 1)] 1)
  (.leafAt [((sp [] 1), .fact 21)] [.input 0] [(19, 32), (22, 24), (26, 28), (35, 36)] [])
  (.leafAt [((sp [(1, (-1)), (19, 1)] 1), .atom 1), ((sp [(1, 1), (19, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(19, 32), (22, 24), (26, 28), (35, 36)] []))
  (.leafAt [((sp [(1, (-1)), (19, 1)] 0), .fact 13), ((sp [(1, 1), (19, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(19, 32), (22, 24), (26, 28), (35, 36)] []))
  (.leafAt [((sp [(1, (-1)), (19, 1)] 0), .fact 13), ((sp [(1, 1), (19, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(19, 32), (22, 24), (26, 28), (35, 36)] []))
  (.leafAt [((sp [(1, (-1)), (19, 1)] 0), .fact 13), ((sp [(1, 1), (19, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(19, 32), (22, 24), (26, 28), (35, 36)] []))
  (.leafAt [((sp [(1, (-1)), (19, 1)] 0), .fact 13), ((sp [(1, 1), (19, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(19, 32), (22, 24), (26, 28), (35, 36)] []))
  (.leafAt [((sp [(7, (-1))] 2), .atom 0), ((sp [(7, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(19, 32), (22, 24), (26, 28), (35, 36)] []))
  (.leafAt [((sp [(1, (-1)), (32, 1)] 0), .fact 15), ((sp [(1, 1), (32, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(1, (-1)), (32, 1)] 0), .fact 15), ((sp [(1, 1), (32, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def padmit_l3 : MLaw := ⟨.le (.get 3 (.var 8)) (.var 2), some 8⟩
def padmit_e3 : MEntry := ⟨padmit_l3, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14], .leafAt [((sp [(2, 1)] 1), .fact 0), ((sp [(2, (-1))] 0), .nat 2)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .term (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 3 (.var 6)) (.const 1)) (.get 3 (.var 6))), .term (.ite (.eq (.var 9) (.var 6)) (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 3 (.var 6)) (.const 1)) (.get 3 (.var 6))) (.get 3 (.var 9))), .cell 0 (sp [(3, 1)] 0), .cell 1 (sp [(4, 1)] 0), .cell 2 (sp [(5, 1)] 0), .cell 3 (sp [(6, 1)] 0), .cell 0 (sp [(4, 1)] 0), .cell 0 (sp [(5, 1)] 0), .cell 0 (sp [(6, 1)] 0), .cell 0 (sp [(9, 1)] 0), .cell 1 (sp [(3, 1)] 0), .cell 1 (sp [(5, 1)] 0), .cell 1 (sp [(6, 1)] 0), .cell 1 (sp [(9, 1)] 0), .cell 2 (sp [(3, 1)] 0), .cell 2 (sp [(4, 1)] 0), .cell 2 (sp [(6, 1)] 0), .cell 2 (sp [(9, 1)] 0), .cell 3 (sp [(3, 1)] 0), .cell 3 (sp [(4, 1)] 0), .cell 3 (sp [(5, 1)] 0), .cell 3 (sp [(9, 1)] 0)], .split (sp [(6, (-1)), (9, 1)] 0)
  (.split (sp [(6, 1), (9, (-1))] 0)
  (.split (sp [(7, 1)] (-1))
  (.split (sp [(7, (-1))] 1)
  (.split (sp [(17, 1)] 0)
  (.split (sp [(0, (-1)), (18, 1)] 1)
  (.split (sp [(1, (-1)), (19, 1)] 1)
  (.split (sp [(2, (-1)), (20, 1)] 1)
  (.leafAt [((sp [] 1), .fact 21)] [.input 0] [(20, 36), (23, 24), (27, 28), (31, 32)] [])
  (.leafAt [((sp [(2, (-1)), (20, 1)] 0), .fact 19), ((sp [(2, 1), (20, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(20, 36), (23, 24), (27, 28), (31, 32)] []))
  (.leafAt [((sp [(2, (-1)), (20, 1)] 0), .fact 19), ((sp [(2, 1), (20, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(20, 36), (23, 24), (27, 28), (31, 32)] []))
  (.leafAt [((sp [(2, (-1)), (20, 1)] 0), .fact 19), ((sp [(2, 1), (20, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(20, 36), (23, 24), (27, 28), (31, 32)] []))
  (.leafAt [((sp [(2, (-1)), (20, 1)] 0), .fact 19), ((sp [(2, 1), (20, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(20, 36), (23, 24), (27, 28), (31, 32)] []))
  (.leafAt [((sp [(2, (-1)), (20, 1)] 0), .fact 19), ((sp [(2, 1), (20, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(20, 36), (23, 24), (27, 28), (31, 32)] []))
  (.leafAt [((sp [(7, (-1))] 2), .atom 0), ((sp [(7, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(20, 36), (23, 24), (27, 28), (31, 32)] []))
  (.leafAt [((sp [(2, (-1)), (36, 1)] 0), .fact 20), ((sp [(2, 1), (36, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(2, (-1)), (36, 1)] 0), .fact 20), ((sp [(2, 1), (36, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def padmit_proof : List MEntry := [padmit_e0, padmit_e1, padmit_e2, padmit_e3]
theorem padmit_check : checkFMMachine padmit_machine padmit_proof = true := by decide +kernel
theorem padmit_laws : ∀ ρ M, FMReach padmit_machine ρ M → ∀ e ∈ padmit_proof, e.law.Holds ρ M :=
  fmmachine_sound padmit_machine padmit_proof padmit_check
namespace padmit
abbrev «d» : Nat := 0
abbrev «hr» : Nat := 1
abbrev «dm» : Nat := 2
abbrev «Acct» : Nat := 0
abbrev «Day» : Nat := 1
abbrev «Hour» : Nat := 2
abbrev «Dom» : Nat := 3
/-- once_per_account: every Acct count <= its cap -/
theorem law0 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach padmit_machine ρ μ) : ∀ k : Nat, (μ «Acct» (k)) ≤ 1 := by
  have hl : padmit_l0.Holds ρ μ := padmit_laws ρ μ h padmit_e0 (by simp [padmit_proof])
  exact fun k => (evalC_iff (upd ρ 8 k) μ padmit_l0.holds).mp (hl k)
/-- day_cap: every Day count <= its cap -/
theorem law1 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach padmit_machine ρ μ) : ∀ k : Nat, (μ «Day» (k)) ≤ ρ «d» := by
  have hl : padmit_l1.Holds ρ μ := padmit_laws ρ μ h padmit_e1 (by simp [padmit_proof])
  exact fun k => (evalC_iff (upd ρ 8 k) μ padmit_l1.holds).mp (hl k)
/-- hour_cap: every Hour count <= its cap -/
theorem law2 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach padmit_machine ρ μ) : ∀ k : Nat, (μ «Hour» (k)) ≤ ρ «hr» := by
  have hl : padmit_l2.Holds ρ μ := padmit_laws ρ μ h padmit_e2 (by simp [padmit_proof])
  exact fun k => (evalC_iff (upd ρ 8 k) μ padmit_l2.holds).mp (hl k)
/-- dom_cap: every Dom count <= its cap -/
theorem law3 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach padmit_machine ρ μ) : ∀ k : Nat, (μ «Dom» (k)) ≤ ρ «dm» := by
  have hl : padmit_l3.Holds ρ μ := padmit_laws ρ μ h padmit_e3 (by simp [padmit_proof])
  exact fun k => (evalC_iff (upd ρ 8 k) μ padmit_l3.holds).mp (hl k)
end padmit

-- Progress: admit: an account under every cap gets its grant
def admit_grant : Progress := ⟨.and (.lt (.get 0 (.var 11)) (.const 1)) (.and (.lt (.get 1 (.var 12)) (.var 0)) (.and (.lt (.get 2 (.var 13)) (.var 1)) (.lt (.get 3 (.var 14)) (.var 2)))),
  .eq (.get 4 (.var 11)) (.const 1),
  [(3, .var 11), (4, .var 12), (5, .var 13), (6, .var 14), (7, .const 1)],
  [],
  [(0, 4), (1, 5), (2, 6), (3, 7)],
  [(0, .var 11), (0, .var 12), (0, .var 13), (0, .var 14), (1, .var 11), (1, .var 12), (1, .var 13), (1, .var 14), (2, .var 11), (2, .var 12), (2, .var 13), (2, .var 14), (3, .var 11), (3, .var 12), (3, .var 13), (3, .var 14)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .cell 0 (sp [(11, 1)] 0), .cell 0 (sp [(12, 1)] 0), .cell 0 (sp [(13, 1)] 0), .cell 0 (sp [(14, 1)] 0), .cell 1 (sp [(11, 1)] 0), .cell 1 (sp [(12, 1)] 0), .cell 1 (sp [(13, 1)] 0), .cell 1 (sp [(14, 1)] 0), .cell 2 (sp [(11, 1)] 0), .cell 2 (sp [(12, 1)] 0), .cell 2 (sp [(13, 1)] 0), .cell 2 (sp [(14, 1)] 0), .cell 3 (sp [(11, 1)] 0), .cell 3 (sp [(12, 1)] 0), .cell 3 (sp [(13, 1)] 0), .cell 3 (sp [(14, 1)] 0)], .leafAt [((sp [] 1), .fact 17)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .term (.ite (.and (.eq (.const 1) (.const 1)) (.and (.lt (.get 0 (.var 11)) (.const 1)) (.and (.lt (.get 1 (.var 12)) (.var 0)) (.and (.lt (.get 2 (.var 13)) (.var 1)) (.lt (.get 3 (.var 14)) (.var 2)))))) (.add (.get 0 (.var 11)) (.const 1)) (.get 0 (.var 11))), .term (.ite (.eq (.var 11) (.var 11)) (.ite (.and (.eq (.const 1) (.const 1)) (.and (.lt (.get 0 (.var 11)) (.const 1)) (.and (.lt (.get 1 (.var 12)) (.var 0)) (.and (.lt (.get 2 (.var 13)) (.var 1)) (.lt (.get 3 (.var 14)) (.var 2)))))) (.add (.get 0 (.var 11)) (.const 1)) (.get 0 (.var 11))) (.get 0 (.var 11))), .cell 0 (sp [(11, 1)] 0), .cell 1 (sp [(12, 1)] 0), .cell 2 (sp [(13, 1)] 0), .cell 3 (sp [(14, 1)] 0), .cell 0 (sp [(12, 1)] 0), .cell 0 (sp [(13, 1)] 0), .cell 0 (sp [(14, 1)] 0), .cell 1 (sp [(11, 1)] 0), .cell 1 (sp [(13, 1)] 0), .cell 1 (sp [(14, 1)] 0), .cell 2 (sp [(11, 1)] 0), .cell 2 (sp [(12, 1)] 0), .cell 2 (sp [(14, 1)] 0), .cell 3 (sp [(11, 1)] 0), .cell 3 (sp [(12, 1)] 0), .cell 3 (sp [(13, 1)] 0)], .split (sp [(17, 1)] 0)
  (.split (sp [(0, (-1)), (18, 1)] 1)
  (.split (sp [(1, (-1)), (19, 1)] 1)
  (.split (sp [(2, (-1)), (20, 1)] 1)
  (.leafAt [((sp [(17, 1)] 1), .fact 17), ((sp [(17, (-1))] 0), .nat 17)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leafAt [((sp [(2, 1), (20, (-1))] 0), .atom 0), ((sp [(2, (-1)), (20, 1)] 1), .fact 16)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(1, 1), (19, (-1))] 0), .atom 0), ((sp [(1, (-1)), (19, 1)] 1), .fact 16)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(0, 1), (18, (-1))] 0), .atom 0), ((sp [(0, (-1)), (18, 1)] 1), .fact 16)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(17, (-1))] 1), .atom 0), ((sp [(17, 1)] 0), .fact 16)] [.input 0, .input 1, .combine 1 0 1 1] [] []))⟩
theorem admit_grant_holds : ProgressHolds padmit_machine admit_grant :=
  progress_sound padmit_machine padmit_proof admit_grant padmit_check (by decide +kernel)
-- TAMPERED: even with the day full (false): the proof above offered for it. Lean computes the check to false.
def admit_grant_tampered : Progress := ⟨.and (.lt (.get 0 (.var 11)) (.const 1)) (.and (.lt (.get 2 (.var 13)) (.var 1)) (.lt (.get 3 (.var 14)) (.var 2))),
  .eq (.get 4 (.var 11)) (.const 1),
  [(3, .var 11), (4, .var 12), (5, .var 13), (6, .var 14), (7, .const 1)],
  [],
  [(0, 4), (1, 5), (2, 6), (3, 7)],
  [(0, .var 11), (0, .var 12), (0, .var 13), (0, .var 14), (1, .var 11), (1, .var 12), (1, .var 13), (1, .var 14), (2, .var 11), (2, .var 12), (2, .var 13), (2, .var 14), (3, .var 11), (3, .var 12), (3, .var 13), (3, .var 14)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .cell 0 (sp [(11, 1)] 0), .cell 0 (sp [(12, 1)] 0), .cell 0 (sp [(13, 1)] 0), .cell 0 (sp [(14, 1)] 0), .cell 1 (sp [(11, 1)] 0), .cell 1 (sp [(12, 1)] 0), .cell 1 (sp [(13, 1)] 0), .cell 1 (sp [(14, 1)] 0), .cell 2 (sp [(11, 1)] 0), .cell 2 (sp [(12, 1)] 0), .cell 2 (sp [(13, 1)] 0), .cell 2 (sp [(14, 1)] 0), .cell 3 (sp [(11, 1)] 0), .cell 3 (sp [(12, 1)] 0), .cell 3 (sp [(13, 1)] 0), .cell 3 (sp [(14, 1)] 0)], .leafAt [((sp [] 1), .fact 17)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .term (.ite (.and (.eq (.const 1) (.const 1)) (.and (.lt (.get 0 (.var 11)) (.const 1)) (.and (.lt (.get 1 (.var 12)) (.var 0)) (.and (.lt (.get 2 (.var 13)) (.var 1)) (.lt (.get 3 (.var 14)) (.var 2)))))) (.add (.get 0 (.var 11)) (.const 1)) (.get 0 (.var 11))), .term (.ite (.eq (.var 11) (.var 11)) (.ite (.and (.eq (.const 1) (.const 1)) (.and (.lt (.get 0 (.var 11)) (.const 1)) (.and (.lt (.get 1 (.var 12)) (.var 0)) (.and (.lt (.get 2 (.var 13)) (.var 1)) (.lt (.get 3 (.var 14)) (.var 2)))))) (.add (.get 0 (.var 11)) (.const 1)) (.get 0 (.var 11))) (.get 0 (.var 11))), .cell 0 (sp [(11, 1)] 0), .cell 1 (sp [(12, 1)] 0), .cell 2 (sp [(13, 1)] 0), .cell 3 (sp [(14, 1)] 0), .cell 0 (sp [(12, 1)] 0), .cell 0 (sp [(13, 1)] 0), .cell 0 (sp [(14, 1)] 0), .cell 1 (sp [(11, 1)] 0), .cell 1 (sp [(13, 1)] 0), .cell 1 (sp [(14, 1)] 0), .cell 2 (sp [(11, 1)] 0), .cell 2 (sp [(12, 1)] 0), .cell 2 (sp [(14, 1)] 0), .cell 3 (sp [(11, 1)] 0), .cell 3 (sp [(12, 1)] 0), .cell 3 (sp [(13, 1)] 0)], .split (sp [(17, 1)] 0)
  (.split (sp [(0, (-1)), (18, 1)] 1)
  (.split (sp [(1, (-1)), (19, 1)] 1)
  (.split (sp [(2, (-1)), (20, 1)] 1)
  (.leafAt [((sp [(17, 1)] 1), .fact 17), ((sp [(17, (-1))] 0), .nat 17)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leafAt [((sp [(2, 1), (20, (-1))] 0), .atom 0), ((sp [(2, (-1)), (20, 1)] 1), .fact 16)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(1, 1), (19, (-1))] 0), .atom 0), ((sp [(1, (-1)), (19, 1)] 1), .fact 16)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(0, 1), (18, (-1))] 0), .atom 0), ((sp [(0, (-1)), (18, 1)] 1), .fact 16)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(17, (-1))] 1), .atom 0), ((sp [(17, 1)] 0), .fact 16)] [.input 0, .input 1, .combine 1 0 1 1] [] []))⟩
example : checkProgress padmit_machine padmit_proof admit_grant_tampered = false := by decide +kernel

-- admit: once_per_account: every Acct count <= its cap; day_cap: every Day count <= its cap; hour_cap: every Hour count <= its cap; dom_cap: every Dom count <= its cap, with flags granted  (variables 0 d, 1 hr, 2 dm, 3 acct, 4 day, 5 hour, 6 dom, 7 ok, 8 k, 9 k#, 10 #, 11 ?granted, 12 A, 13 D, 14 H, 15 M; maps 0 Acct, 1 Day, 2 Hour, 3 Dom, 4 Acct', 5 Day', 6 Hour', 7 Dom')
def pfadmit_machine : FMMachine := ⟨⟨[3, 4, 5, 6, 7],
  [],
  [(0, 0), (1, 0), (2, 0), (3, 0)],
  [],
  [(0, .var 3, .ite (.eq (.var 11) (.const 1)) (.add (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3))), (1, .var 4, .ite (.eq (.var 11) (.const 1)) (.add (.get 1 (.var 4)) (.const 1)) (.get 1 (.var 4))), (2, .var 5, .ite (.eq (.var 11) (.const 1)) (.add (.get 2 (.var 5)) (.const 1)) (.get 2 (.var 5))), (3, .var 6, .ite (.eq (.var 11) (.const 1)) (.add (.get 3 (.var 6)) (.const 1)) (.get 3 (.var 6)))],
  .le (.const 0) (.const 0),
  .or (.eq (.var 7) (.const 0)) (.eq (.var 7) (.const 1))⟩,
  [(11, .and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2))))))]⟩
def pfadmit_l0 : MLaw := ⟨.le (.get 0 (.var 8)) (.const 1), some 8⟩
def pfadmit_e0 : MEntry := ⟨pfadmit_l0, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15], .leafAt [((sp [] 1), .fact 0)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15, .term (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3))), .term (.ite (.eq (.var 9) (.var 3)) (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 0 (.var 3)) (.const 1)) (.get 0 (.var 3))) (.get 0 (.var 9))), .cell 0 (sp [(3, 1)] 0), .cell 1 (sp [(4, 1)] 0), .cell 2 (sp [(5, 1)] 0), .cell 3 (sp [(6, 1)] 0), .cell 0 (sp [(4, 1)] 0), .cell 0 (sp [(5, 1)] 0), .cell 0 (sp [(6, 1)] 0), .cell 0 (sp [(9, 1)] 0), .cell 1 (sp [(3, 1)] 0), .cell 1 (sp [(5, 1)] 0), .cell 1 (sp [(6, 1)] 0), .cell 1 (sp [(9, 1)] 0), .cell 2 (sp [(3, 1)] 0), .cell 2 (sp [(4, 1)] 0), .cell 2 (sp [(6, 1)] 0), .cell 2 (sp [(9, 1)] 0), .cell 3 (sp [(3, 1)] 0), .cell 3 (sp [(4, 1)] 0), .cell 3 (sp [(5, 1)] 0), .cell 3 (sp [(9, 1)] 0)], .split (sp [(3, (-1)), (9, 1)] 0)
  (.split (sp [(3, 1), (9, (-1))] 0)
  (.split (sp [(7, 1)] (-1))
  (.split (sp [(7, (-1))] 1)
  (.split (sp [(18, 1)] 0)
  (.split (sp [(0, (-1)), (19, 1)] 1)
  (.split (sp [(1, (-1)), (20, 1)] 1)
  (.split (sp [(2, (-1)), (21, 1)] 1)
  (.leafAt [((sp [] 1), .fact 21)] [.input 0] [(18, 25), (26, 29), (30, 33), (34, 37)] [])
  (.leafAt [((sp [(18, 1)] 0), .atom 3), ((sp [(18, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(18, 25), (26, 29), (30, 33), (34, 37)] []))
  (.leafAt [((sp [(18, 1)] 0), .atom 2), ((sp [(18, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(18, 25), (26, 29), (30, 33), (34, 37)] []))
  (.leafAt [((sp [(18, 1)] 0), .atom 1), ((sp [(18, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(18, 25), (26, 29), (30, 33), (34, 37)] []))
  (.leafAt [((sp [(18, 1)] (-1)), .fact 1), ((sp [(18, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(18, 25), (26, 29), (30, 33), (34, 37)] []))
  (.leafAt [((sp [(18, 1)] (-1)), .fact 1), ((sp [(18, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(18, 25), (26, 29), (30, 33), (34, 37)] []))
  (.leafAt [((sp [(7, (-1))] 2), .atom 0), ((sp [(7, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(18, 25), (26, 29), (30, 33), (34, 37)] []))
  (.leafAt [((sp [(25, 1)] (-1)), .fact 5), ((sp [(25, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(25, 1)] (-1)), .fact 5), ((sp [(25, (-1))] 2), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def pfadmit_l1 : MLaw := ⟨.le (.get 1 (.var 8)) (.var 0), some 8⟩
def pfadmit_e1 : MEntry := ⟨pfadmit_l1, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15], .leafAt [((sp [(0, 1)] 1), .fact 0), ((sp [(0, (-1))] 0), .nat 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15, .term (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 1 (.var 4)) (.const 1)) (.get 1 (.var 4))), .term (.ite (.eq (.var 9) (.var 4)) (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 1 (.var 4)) (.const 1)) (.get 1 (.var 4))) (.get 1 (.var 9))), .cell 0 (sp [(3, 1)] 0), .cell 1 (sp [(4, 1)] 0), .cell 2 (sp [(5, 1)] 0), .cell 3 (sp [(6, 1)] 0), .cell 0 (sp [(4, 1)] 0), .cell 0 (sp [(5, 1)] 0), .cell 0 (sp [(6, 1)] 0), .cell 0 (sp [(9, 1)] 0), .cell 1 (sp [(3, 1)] 0), .cell 1 (sp [(5, 1)] 0), .cell 1 (sp [(6, 1)] 0), .cell 1 (sp [(9, 1)] 0), .cell 2 (sp [(3, 1)] 0), .cell 2 (sp [(4, 1)] 0), .cell 2 (sp [(6, 1)] 0), .cell 2 (sp [(9, 1)] 0), .cell 3 (sp [(3, 1)] 0), .cell 3 (sp [(4, 1)] 0), .cell 3 (sp [(5, 1)] 0), .cell 3 (sp [(9, 1)] 0)], .split (sp [(4, (-1)), (9, 1)] 0)
  (.split (sp [(4, 1), (9, (-1))] 0)
  (.split (sp [(7, 1)] (-1))
  (.split (sp [(7, (-1))] 1)
  (.split (sp [(18, 1)] 0)
  (.split (sp [(0, (-1)), (19, 1)] 1)
  (.split (sp [(1, (-1)), (20, 1)] 1)
  (.split (sp [(2, (-1)), (21, 1)] 1)
  (.leafAt [((sp [] 1), .fact 21)] [.input 0] [(19, 29), (22, 25), (31, 33), (35, 37)] [])
  (.leafAt [((sp [(0, (-1)), (19, 1)] 1), .atom 2), ((sp [(0, 1), (19, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(19, 29), (22, 25), (31, 33), (35, 37)] []))
  (.leafAt [((sp [(0, (-1)), (19, 1)] 1), .atom 1), ((sp [(0, 1), (19, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(19, 29), (22, 25), (31, 33), (35, 37)] []))
  (.leafAt [((sp [(0, (-1)), (19, 1)] 0), .fact 7), ((sp [(0, 1), (19, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(19, 29), (22, 25), (31, 33), (35, 37)] []))
  (.leafAt [((sp [(0, (-1)), (19, 1)] 0), .fact 7), ((sp [(0, 1), (19, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(19, 29), (22, 25), (31, 33), (35, 37)] []))
  (.leafAt [((sp [(0, (-1)), (19, 1)] 0), .fact 7), ((sp [(0, 1), (19, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(19, 29), (22, 25), (31, 33), (35, 37)] []))
  (.leafAt [((sp [(7, (-1))] 2), .atom 0), ((sp [(7, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(19, 29), (22, 25), (31, 33), (35, 37)] []))
  (.leafAt [((sp [(0, (-1)), (29, 1)] 0), .fact 10), ((sp [(0, 1), (29, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(0, (-1)), (29, 1)] 0), .fact 10), ((sp [(0, 1), (29, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def pfadmit_l2 : MLaw := ⟨.le (.get 2 (.var 8)) (.var 1), some 8⟩
def pfadmit_e2 : MEntry := ⟨pfadmit_l2, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15], .leafAt [((sp [(1, 1)] 1), .fact 0), ((sp [(1, (-1))] 0), .nat 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15, .term (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 2 (.var 5)) (.const 1)) (.get 2 (.var 5))), .term (.ite (.eq (.var 9) (.var 5)) (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 2 (.var 5)) (.const 1)) (.get 2 (.var 5))) (.get 2 (.var 9))), .cell 0 (sp [(3, 1)] 0), .cell 1 (sp [(4, 1)] 0), .cell 2 (sp [(5, 1)] 0), .cell 3 (sp [(6, 1)] 0), .cell 0 (sp [(4, 1)] 0), .cell 0 (sp [(5, 1)] 0), .cell 0 (sp [(6, 1)] 0), .cell 0 (sp [(9, 1)] 0), .cell 1 (sp [(3, 1)] 0), .cell 1 (sp [(5, 1)] 0), .cell 1 (sp [(6, 1)] 0), .cell 1 (sp [(9, 1)] 0), .cell 2 (sp [(3, 1)] 0), .cell 2 (sp [(4, 1)] 0), .cell 2 (sp [(6, 1)] 0), .cell 2 (sp [(9, 1)] 0), .cell 3 (sp [(3, 1)] 0), .cell 3 (sp [(4, 1)] 0), .cell 3 (sp [(5, 1)] 0), .cell 3 (sp [(9, 1)] 0)], .split (sp [(5, (-1)), (9, 1)] 0)
  (.split (sp [(5, 1), (9, (-1))] 0)
  (.split (sp [(7, 1)] (-1))
  (.split (sp [(7, (-1))] 1)
  (.split (sp [(18, 1)] 0)
  (.split (sp [(0, (-1)), (19, 1)] 1)
  (.split (sp [(1, (-1)), (20, 1)] 1)
  (.split (sp [(2, (-1)), (21, 1)] 1)
  (.leafAt [((sp [] 1), .fact 21)] [.input 0] [(20, 33), (23, 25), (27, 29), (36, 37)] [])
  (.leafAt [((sp [(1, (-1)), (20, 1)] 1), .atom 1), ((sp [(1, 1), (20, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(20, 33), (23, 25), (27, 29), (36, 37)] []))
  (.leafAt [((sp [(1, (-1)), (20, 1)] 0), .fact 13), ((sp [(1, 1), (20, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(20, 33), (23, 25), (27, 29), (36, 37)] []))
  (.leafAt [((sp [(1, (-1)), (20, 1)] 0), .fact 13), ((sp [(1, 1), (20, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(20, 33), (23, 25), (27, 29), (36, 37)] []))
  (.leafAt [((sp [(1, (-1)), (20, 1)] 0), .fact 13), ((sp [(1, 1), (20, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(20, 33), (23, 25), (27, 29), (36, 37)] []))
  (.leafAt [((sp [(1, (-1)), (20, 1)] 0), .fact 13), ((sp [(1, 1), (20, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(20, 33), (23, 25), (27, 29), (36, 37)] []))
  (.leafAt [((sp [(7, (-1))] 2), .atom 0), ((sp [(7, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(20, 33), (23, 25), (27, 29), (36, 37)] []))
  (.leafAt [((sp [(1, (-1)), (33, 1)] 0), .fact 15), ((sp [(1, 1), (33, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(1, (-1)), (33, 1)] 0), .fact 15), ((sp [(1, 1), (33, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def pfadmit_l3 : MLaw := ⟨.le (.get 3 (.var 8)) (.var 2), some 8⟩
def pfadmit_e3 : MEntry := ⟨pfadmit_l3, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15], .leafAt [((sp [(2, 1)] 1), .fact 0), ((sp [(2, (-1))] 0), .nat 2)] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15, .term (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 3 (.var 6)) (.const 1)) (.get 3 (.var 6))), .term (.ite (.eq (.var 9) (.var 6)) (.ite (.and (.eq (.var 7) (.const 1)) (.and (.lt (.get 0 (.var 3)) (.const 1)) (.and (.lt (.get 1 (.var 4)) (.var 0)) (.and (.lt (.get 2 (.var 5)) (.var 1)) (.lt (.get 3 (.var 6)) (.var 2)))))) (.add (.get 3 (.var 6)) (.const 1)) (.get 3 (.var 6))) (.get 3 (.var 9))), .cell 0 (sp [(3, 1)] 0), .cell 1 (sp [(4, 1)] 0), .cell 2 (sp [(5, 1)] 0), .cell 3 (sp [(6, 1)] 0), .cell 0 (sp [(4, 1)] 0), .cell 0 (sp [(5, 1)] 0), .cell 0 (sp [(6, 1)] 0), .cell 0 (sp [(9, 1)] 0), .cell 1 (sp [(3, 1)] 0), .cell 1 (sp [(5, 1)] 0), .cell 1 (sp [(6, 1)] 0), .cell 1 (sp [(9, 1)] 0), .cell 2 (sp [(3, 1)] 0), .cell 2 (sp [(4, 1)] 0), .cell 2 (sp [(6, 1)] 0), .cell 2 (sp [(9, 1)] 0), .cell 3 (sp [(3, 1)] 0), .cell 3 (sp [(4, 1)] 0), .cell 3 (sp [(5, 1)] 0), .cell 3 (sp [(9, 1)] 0)], .split (sp [(6, (-1)), (9, 1)] 0)
  (.split (sp [(6, 1), (9, (-1))] 0)
  (.split (sp [(7, 1)] (-1))
  (.split (sp [(7, (-1))] 1)
  (.split (sp [(18, 1)] 0)
  (.split (sp [(0, (-1)), (19, 1)] 1)
  (.split (sp [(1, (-1)), (20, 1)] 1)
  (.split (sp [(2, (-1)), (21, 1)] 1)
  (.leafAt [((sp [] 1), .fact 21)] [.input 0] [(21, 37), (24, 25), (28, 29), (32, 33)] [])
  (.leafAt [((sp [(2, (-1)), (21, 1)] 0), .fact 19), ((sp [(2, 1), (21, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(21, 37), (24, 25), (28, 29), (32, 33)] []))
  (.leafAt [((sp [(2, (-1)), (21, 1)] 0), .fact 19), ((sp [(2, 1), (21, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(21, 37), (24, 25), (28, 29), (32, 33)] []))
  (.leafAt [((sp [(2, (-1)), (21, 1)] 0), .fact 19), ((sp [(2, 1), (21, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(21, 37), (24, 25), (28, 29), (32, 33)] []))
  (.leafAt [((sp [(2, (-1)), (21, 1)] 0), .fact 19), ((sp [(2, 1), (21, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(21, 37), (24, 25), (28, 29), (32, 33)] []))
  (.leafAt [((sp [(2, (-1)), (21, 1)] 0), .fact 19), ((sp [(2, 1), (21, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [(21, 37), (24, 25), (28, 29), (32, 33)] []))
  (.leafAt [((sp [(7, (-1))] 2), .atom 0), ((sp [(7, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(21, 37), (24, 25), (28, 29), (32, 33)] []))
  (.leafAt [((sp [(2, (-1)), (37, 1)] 0), .fact 20), ((sp [(2, 1), (37, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(2, (-1)), (37, 1)] 0), .fact 20), ((sp [(2, 1), (37, (-1))] 1), .fact 21)] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
def pfadmit_proof : List MEntry := [pfadmit_e0, pfadmit_e1, pfadmit_e2, pfadmit_e3]
theorem pfadmit_check : checkFMMachine pfadmit_machine pfadmit_proof = true := by decide +kernel
theorem pfadmit_laws : ∀ ρ M, FMReach pfadmit_machine ρ M → ∀ e ∈ pfadmit_proof, e.law.Holds ρ M :=
  fmmachine_sound pfadmit_machine pfadmit_proof pfadmit_check
namespace pfadmit
abbrev «d» : Nat := 0
abbrev «hr» : Nat := 1
abbrev «dm» : Nat := 2
abbrev «Acct» : Nat := 0
abbrev «Day» : Nat := 1
abbrev «Hour» : Nat := 2
abbrev «Dom» : Nat := 3
/-- once_per_account: every Acct count <= its cap -/
theorem law0 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach pfadmit_machine ρ μ) : ∀ k : Nat, (μ «Acct» (k)) ≤ 1 := by
  have hl : pfadmit_l0.Holds ρ μ := pfadmit_laws ρ μ h pfadmit_e0 (by simp [pfadmit_proof])
  exact fun k => (evalC_iff (upd ρ 8 k) μ pfadmit_l0.holds).mp (hl k)
/-- day_cap: every Day count <= its cap -/
theorem law1 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach pfadmit_machine ρ μ) : ∀ k : Nat, (μ «Day» (k)) ≤ ρ «d» := by
  have hl : pfadmit_l1.Holds ρ μ := pfadmit_laws ρ μ h pfadmit_e1 (by simp [pfadmit_proof])
  exact fun k => (evalC_iff (upd ρ 8 k) μ pfadmit_l1.holds).mp (hl k)
/-- hour_cap: every Hour count <= its cap -/
theorem law2 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach pfadmit_machine ρ μ) : ∀ k : Nat, (μ «Hour» (k)) ≤ ρ «hr» := by
  have hl : pfadmit_l2.Holds ρ μ := pfadmit_laws ρ μ h pfadmit_e2 (by simp [pfadmit_proof])
  exact fun k => (evalC_iff (upd ρ 8 k) μ pfadmit_l2.holds).mp (hl k)
/-- dom_cap: every Dom count <= its cap -/
theorem law3 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach pfadmit_machine ρ μ) : ∀ k : Nat, (μ «Dom» (k)) ≤ ρ «dm» := by
  have hl : pfadmit_l3.Holds ρ μ := pfadmit_laws ρ μ h pfadmit_e3 (by simp [pfadmit_proof])
  exact fun k => (evalC_iff (upd ρ 8 k) μ pfadmit_l3.holds).mp (hl k)
end pfadmit

-- Progress: admit, the grant as a flag: an account under every cap gets its grant
def fadmit_grant : Progress := ⟨.and (.lt (.get 0 (.var 12)) (.const 1)) (.and (.lt (.get 1 (.var 13)) (.var 0)) (.and (.lt (.get 2 (.var 14)) (.var 1)) (.lt (.get 3 (.var 15)) (.var 2)))),
  .eq (.get 4 (.var 12)) (.const 1),
  [(3, .var 12), (4, .var 13), (5, .var 14), (6, .var 15), (7, .const 1)],
  [],
  [(0, 4), (1, 5), (2, 6), (3, 7)],
  [(0, .var 12), (0, .var 13), (0, .var 14), (0, .var 15), (1, .var 12), (1, .var 13), (1, .var 14), (1, .var 15), (2, .var 12), (2, .var 13), (2, .var 14), (2, .var 15), (3, .var 12), (3, .var 13), (3, .var 14), (3, .var 15)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15, .cell 0 (sp [(12, 1)] 0), .cell 0 (sp [(13, 1)] 0), .cell 0 (sp [(14, 1)] 0), .cell 0 (sp [(15, 1)] 0), .cell 1 (sp [(12, 1)] 0), .cell 1 (sp [(13, 1)] 0), .cell 1 (sp [(14, 1)] 0), .cell 1 (sp [(15, 1)] 0), .cell 2 (sp [(12, 1)] 0), .cell 2 (sp [(13, 1)] 0), .cell 2 (sp [(14, 1)] 0), .cell 2 (sp [(15, 1)] 0), .cell 3 (sp [(12, 1)] 0), .cell 3 (sp [(13, 1)] 0), .cell 3 (sp [(14, 1)] 0), .cell 3 (sp [(15, 1)] 0)], .leafAt [((sp [] 1), .fact 17)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15, .term (.ite (.and (.eq (.const 1) (.const 1)) (.and (.lt (.get 0 (.var 12)) (.const 1)) (.and (.lt (.get 1 (.var 13)) (.var 0)) (.and (.lt (.get 2 (.var 14)) (.var 1)) (.lt (.get 3 (.var 15)) (.var 2)))))) (.add (.get 0 (.var 12)) (.const 1)) (.get 0 (.var 12))), .term (.ite (.eq (.var 12) (.var 12)) (.ite (.and (.eq (.const 1) (.const 1)) (.and (.lt (.get 0 (.var 12)) (.const 1)) (.and (.lt (.get 1 (.var 13)) (.var 0)) (.and (.lt (.get 2 (.var 14)) (.var 1)) (.lt (.get 3 (.var 15)) (.var 2)))))) (.add (.get 0 (.var 12)) (.const 1)) (.get 0 (.var 12))) (.get 0 (.var 12))), .cell 0 (sp [(12, 1)] 0), .cell 1 (sp [(13, 1)] 0), .cell 2 (sp [(14, 1)] 0), .cell 3 (sp [(15, 1)] 0), .cell 0 (sp [(13, 1)] 0), .cell 0 (sp [(14, 1)] 0), .cell 0 (sp [(15, 1)] 0), .cell 1 (sp [(12, 1)] 0), .cell 1 (sp [(14, 1)] 0), .cell 1 (sp [(15, 1)] 0), .cell 2 (sp [(12, 1)] 0), .cell 2 (sp [(13, 1)] 0), .cell 2 (sp [(15, 1)] 0), .cell 3 (sp [(12, 1)] 0), .cell 3 (sp [(13, 1)] 0), .cell 3 (sp [(14, 1)] 0)], .split (sp [(18, 1)] 0)
  (.split (sp [(0, (-1)), (19, 1)] 1)
  (.split (sp [(1, (-1)), (20, 1)] 1)
  (.split (sp [(2, (-1)), (21, 1)] 1)
  (.leafAt [((sp [(18, 1)] 1), .fact 17), ((sp [(18, (-1))] 0), .nat 18)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leafAt [((sp [(2, 1), (21, (-1))] 0), .atom 0), ((sp [(2, (-1)), (21, 1)] 1), .fact 16)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(1, 1), (20, (-1))] 0), .atom 0), ((sp [(1, (-1)), (20, 1)] 1), .fact 16)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(0, 1), (19, (-1))] 0), .atom 0), ((sp [(0, (-1)), (19, 1)] 1), .fact 16)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(18, (-1))] 1), .atom 0), ((sp [(18, 1)] 0), .fact 16)] [.input 0, .input 1, .combine 1 0 1 1] [] []))⟩
theorem fadmit_grant_holds : ProgressHolds pfadmit_machine fadmit_grant :=
  progress_sound pfadmit_machine pfadmit_proof fadmit_grant pfadmit_check (by decide +kernel)

-- isolation: a.Acct[B] = b.Acct[B]  (variables 0 d, 1 hr, 2 dm, 3 Bacct, 4 Bday, 5 Bhour, 6 Bdom, 7 acct, 8 day, 9 hour, 10 dom, 11 ok, 12 who, 13 #; maps 0 a_Acct, 1 a_Day, 2 a_Hour, 3 a_Dom, 4 b_Acct, 5 b_Day, 6 b_Hour, 7 b_Dom)
def peracct_machine : FMMachine := ⟨⟨[7, 8, 9, 10, 11, 12],
  [],
  [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0)],
  [],
  [(0, .var 7, .ite (.and (.eq (.var 11) (.const 1)) (.lt (.get 0 (.var 7)) (.const 1))) (.add (.get 0 (.var 7)) (.const 1)) (.get 0 (.var 7))), (4, .var 7, .ite (.and (.eq (.ite (.eq (.var 12) (.const 1)) (.const 0) (.var 11)) (.const 1)) (.lt (.get 4 (.var 7)) (.const 1))) (.add (.get 4 (.var 7)) (.const 1)) (.get 4 (.var 7)))],
  .le (.const 0) (.const 0),
  .and (.or (.eq (.var 11) (.const 0)) (.eq (.var 11) (.const 1))) (.and (.or (.eq (.ite (.eq (.var 12) (.const 1)) (.const 0) (.var 11)) (.const 0)) (.eq (.ite (.eq (.var 12) (.const 1)) (.const 0) (.var 11)) (.const 1))) (.and (.or (.eq (.var 12) (.const 0)) (.eq (.var 12) (.const 1))) (.or (.and (.eq (.var 12) (.const 0)) (.and (.eq (.var 7) (.var 3)) (.and (.eq (.var 8) (.var 4)) (.and (.eq (.var 9) (.var 5)) (.eq (.var 10) (.var 6)))))) (.and (.eq (.var 12) (.const 1)) (.not (.eq (.var 7) (.var 3)))))))⟩,
  []⟩
def peracct_l0 : MLaw := ⟨.eq (.get 0 (.var 3)) (.get 4 (.var 3)), none⟩
def peracct_e0 : MEntry := ⟨peracct_l0, 13, [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13], .leafAt [((sp [] 1), .fact 0)] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .term (.ite (.eq (.var 12) (.const 1)) (.const 0) (.var 11)), .term (.ite (.and (.eq (.var 11) (.const 1)) (.lt (.get 0 (.var 7)) (.const 1))) (.add (.get 0 (.var 7)) (.const 1)) (.get 0 (.var 7))), .term (.ite (.eq (.var 3) (.var 7)) (.ite (.and (.eq (.var 11) (.const 1)) (.lt (.get 0 (.var 7)) (.const 1))) (.add (.get 0 (.var 7)) (.const 1)) (.get 0 (.var 7))) (.get 0 (.var 3))), .term (.ite (.and (.eq (.ite (.eq (.var 12) (.const 1)) (.const 0) (.var 11)) (.const 1)) (.lt (.get 4 (.var 7)) (.const 1))) (.add (.get 4 (.var 7)) (.const 1)) (.get 4 (.var 7))), .term (.ite (.eq (.var 3) (.var 7)) (.ite (.and (.eq (.ite (.eq (.var 12) (.const 1)) (.const 0) (.var 11)) (.const 1)) (.lt (.get 4 (.var 7)) (.const 1))) (.add (.get 4 (.var 7)) (.const 1)) (.get 4 (.var 7))) (.get 4 (.var 3))), .cell 0 (sp [(7, 1)] 0), .cell 0 (sp [(3, 1)] 0), .cell 4 (sp [(3, 1)] 0), .cell 4 (sp [(7, 1)] 0)], .split (sp [(3, 1), (7, (-1))] 0)
  (.split (sp [(3, (-1)), (7, 1)] 0)
  (.split (sp [(11, 1)] (-1))
  (.split (sp [(11, (-1))] 1)
  (.split (sp [(19, 1)] 0)
  (.split (sp [(12, (-1))] 1)
  (.leafAt [((sp [] 1), .fact 0)] [.input 0] [(19, 20), (21, 22)] [])
  (.split (sp [(22, 1)] 0)
  (.split (sp [(19, 1), (22, (-1))] 0)
  (.leafAt [((sp [(22, 1)] 0), .atom 1), ((sp [(19, 1), (22, (-1))] 1), .fact 2), ((sp [(19, (-1))] 0), .nat 19)] [.input 0, .input 1, .input 2, .combine 1 2 1 1, .combine 3 0 1 1] [(19, 20), (21, 22)] [])
  (.leafAt [((sp [(19, 1)] 0), .atom 3), ((sp [(19, (-1)), (22, 1)] 1), .atom 0), ((sp [(22, (-1))] 0), .nat 22)] [.input 0, .input 1, .input 2, .combine 1 0 1 1, .combine 3 2 1 1] [(19, 20), (21, 22)] []))
  (.leafAt [((sp [(19, 1)] 0), .atom 2), ((sp [(22, (-1))] 1), .atom 0), ((sp [(20, (-1)), (21, 1)] 0), .fact 1), ((sp [(19, (-1)), (20, 1)] 0), .eq 0), ((sp [(21, (-1)), (22, 1)] 0), .eq 1)] [.input 0, .input 1, .input 2, .input 3, .input 4, .combine 3 0 1 1, .combine 5 2 1 1, .combine 4 6 1 1, .combine 1 7 1 1] [(19, 20), (21, 22)] [])))
  (.split (sp [(12, (-1))] 1)
  (.leafAt [((sp [] 1), .fact 0)] [.input 0] [(19, 20), (21, 22)] [])
  (.split (sp [(22, 1)] 0)
  (.leafAt [((sp [(19, (-1))] 1), .atom 2), ((sp [(22, 1)] 0), .atom 0), ((sp [(20, 1), (21, (-1))] 0), .fact 1), ((sp [(19, 1), (20, (-1))] 0), .eq 0), ((sp [(21, 1), (22, (-1))] 0), .eq 1)] [.input 0, .input 1, .input 2, .input 3, .input 4, .combine 4 1 1 1, .combine 3 2 1 1, .combine 0 6 1 1, .combine 7 5 1 1] [(19, 20), (21, 22)] [])
  (.split (sp [(19, 1), (22, (-1))] 0)
  (.leafAt [((sp [(20, (-1)), (21, 1)] 0), .fact 1), ((sp [(19, 1), (22, (-1))] 1), .fact 2), ((sp [(19, (-1)), (20, 1)] 0), .eq 0), ((sp [(21, (-1)), (22, 1)] 0), .eq 1)] [.input 0, .input 1, .input 2, .input 3, .combine 2 0 1 1, .combine 1 4 1 1, .combine 5 3 1 1] [(19, 20), (21, 22)] [])
  (.leafAt [((sp [(19, (-1)), (22, 1)] 1), .atom 0), ((sp [(20, 1), (21, (-1))] 0), .fact 1), ((sp [(19, 1), (20, (-1))] 0), .eq 0), ((sp [(21, 1), (22, (-1))] 0), .eq 1)] [.input 0, .input 1, .input 2, .input 3, .combine 2 1 1 1, .combine 0 4 1 1, .combine 5 3 1 1] [(19, 20), (21, 22)] [])))))
  (.split (sp [(12, (-1))] 1)
  (.leafAt [((sp [] 1), .fact 0)] [.input 0] [(19, 20), (21, 22)] [])
  (.split (sp [(19, 1), (22, (-1))] 0)
  (.leafAt [((sp [(20, (-1)), (21, 1)] 0), .fact 1), ((sp [(19, 1), (22, (-1))] 1), .fact 2), ((sp [(19, (-1)), (20, 1)] 0), .eq 0), ((sp [(21, (-1)), (22, 1)] 0), .eq 1)] [.input 0, .input 1, .input 2, .input 3, .combine 2 0 1 1, .combine 1 4 1 1, .combine 5 3 1 1] [(19, 20), (21, 22)] [])
  (.leafAt [((sp [(19, (-1)), (22, 1)] 1), .atom 0), ((sp [(20, 1), (21, (-1))] 0), .fact 1), ((sp [(19, 1), (20, (-1))] 0), .eq 0), ((sp [(21, 1), (22, (-1))] 0), .eq 1)] [.input 0, .input 1, .input 2, .input 3, .combine 2 1 1 1, .combine 0 4 1 1, .combine 5 3 1 1] [(19, 20), (21, 22)] []))))
  (.leafAt [((sp [(11, (-1))] 2), .atom 0), ((sp [(11, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [(19, 20), (21, 22)] []))
  (.split (sp [(20, 1), (21, (-1))] 0)
  (.leafAt [((sp [(20, (-1)), (21, 1)] 0), .fact 1), ((sp [(20, 1), (21, (-1))] 1), .fact 2)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(20, (-1)), (21, 1)] 1), .atom 0), ((sp [(20, 1), (21, (-1))] 0), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))
  (.split (sp [(20, 1), (21, (-1))] 0)
  (.leafAt [((sp [(20, (-1)), (21, 1)] 0), .fact 1), ((sp [(20, 1), (21, (-1))] 1), .fact 2)] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leafAt [((sp [(20, (-1)), (21, 1)] 1), .atom 0), ((sp [(20, 1), (21, (-1))] 0), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩
def peracct_proof : List MEntry := [peracct_e0]
theorem peracct_check : checkFMMachine peracct_machine peracct_proof = true := by decide +kernel
theorem peracct_laws : ∀ ρ M, FMReach peracct_machine ρ M → ∀ e ∈ peracct_proof, e.law.Holds ρ M :=
  fmmachine_sound peracct_machine peracct_proof peracct_check
namespace peracct
abbrev «Bacct» : Nat := 3
abbrev «a_Acct» : Nat := 0
abbrev «b_Acct» : Nat := 4
/-- a.Acct[B] = b.Acct[B] -/
theorem law0 (ρ : Nat → Nat) (μ : Nat → Nat → Nat) (h : FMReach peracct_machine ρ μ) : (μ «a_Acct» (ρ «Bacct»)) = (μ «b_Acct» (ρ «Bacct»)) := by
  have hl : peracct_l0.Holds ρ μ := peracct_laws ρ μ h peracct_e0 (by simp [peracct_proof])
  exact (evalC_iff ρ μ peracct_l0.holds).mp hl
end peracct

-- spend roll-up, cap m a param: spend <= m count  (variables 0 m, 1 c, 2 spend, 3 count, 4 l_spend, 5 l_count, 6 r_spend, 7 r_count)
def rollupM_fold : Fold := ⟨[1],
  [(2, 4, 6), (3, 5, 7)],
  [(2, .min (.var 1) (.var 0)), (3, .const 1)],
  [(2, .add (.var 4) (.var 6)), (3, .add (.var 5) (.var 7))],
  .le (.const 0) (.const 0),
  .le (.const 0) (.const 0)⟩
def rollupM_proof : FoldProof := [(.le (.var 2) (.prod (.var 0) (.var 3)),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .term (.min (.var 1) (.var 0))], .split (sp [(0, (-1)), (1, 1)] 0)
  (.leafAt [((sp [] 1), .fact 0)] [.input 0] [] [])
  (.leafAt [((sp [] 1), .fact 0)] [.input 0] [] [])),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .mono [0, 5], .mono [0, 7]], .leafAt [((sp [(4, 1), (8, (-1))] 0), .fact 0), ((sp [(6, 1), (9, (-1))] 0), .fact 1), ((sp [(4, (-1)), (6, (-1)), (8, 1), (9, 1)] 1), .fact 2)] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 1 3 1 1] [] []))]
theorem rollupM_laws : ∀ maps ρ, evalC ρ maps rollupM_fold.pre = true → ∀ t, Allowed rollupM_fold ρ maps t →
    ∀ l ∈ rollupM_proof.map (·.1), evalC (foldT rollupM_fold ρ maps t) maps l = true :=
  fold_sound rollupM_fold rollupM_proof (by decide +kernel)

-- budget rule: bounded_loss: s <= b + m @start  (2 columns)
def t0_goal : Goal := ⟨[.var 0, .var 1],
  [.not (.le (.const 0) (.add (.var 0) (.var 1)))]⟩
def t0_tree : Tree :=
  .leafAt [((sp [(0, 1), (1, 1)] 1), .fact 0), ((sp [(0, (-1))] 0), .nat 0), ((sp [(1, (-1))] 0), .nat 1)] [.input 0, .input 1, .input 2, .combine 0 1 1 1, .combine 3 2 1 1] [] []
theorem t0 : ∀ env maps, ¬ ∀ c ∈ t0_goal.hyps, evalC env maps c = true :=
  sound t0_goal t0_tree (by decide +kernel)

-- budget rule: bounded_loss: s <= b + m @step  (6 columns)
def t1_goal : Goal := ⟨[.var 0, .var 1, .var 2, .var 3, .term (.min (.var 3) (.var 2)), .term (.ite (.lt (.var 0) (.var 1)) (.add (.var 0) (.min (.var 3) (.var 2))) (.var 0))],
  [.le (.var 0) (.add (.var 1) (.var 2)), .not (.le (.ite (.lt (.var 0) (.var 1)) (.add (.var 0) (.min (.var 3) (.var 2))) (.var 0)) (.add (.var 1) (.var 2)))]⟩
def t1_tree : Tree :=
  .split (sp [(0, 1), (1, (-1))] 1)
  (.split (sp [(2, (-1)), (3, 1)] 0)
  (.leafAt [((sp [(0, 1), (1, (-1))] 1), .atom 1), ((sp [(2, (-1)), (3, 1)] 0), .atom 0), ((sp [(0, (-1)), (1, 1), (2, 1), (3, (-1))] 1), .fact 1)] [.input 0, .input 1, .input 2, .combine 2 0 1 1, .combine 1 3 1 1] [] [])
  (.leafAt [((sp [(0, 1), (1, (-1))] 1), .atom 1), ((sp [(0, (-1)), (1, 1)] 1), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(0, 1), (1, (-1)), (2, (-1))] 0), .fact 0), ((sp [(0, (-1)), (1, 1), (2, 1)] 1), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
theorem t1 : ∀ env maps, ¬ ∀ c ∈ t1_goal.hyps, evalC env maps c = true :=
  sound t1_goal t1_tree (by decide +kernel)

-- in-flight: in-flight loss: s <= b + 3 × 50 @start  (1 columns)
def t2_goal : Goal := ⟨[.var 0],
  [.not (.le (.const 0) (.add (.var 0) (.const 150)))]⟩
def t2_tree : Tree :=
  .leafAt [((sp [(0, 1)] 151), .fact 0), ((sp [(0, (-1))] 0), .nat 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []
theorem t2 : ∀ env maps, ¬ ∀ c ∈ t2_goal.hyps, evalC env maps c = true :=
  sound t2_goal t2_tree (by decide +kernel)

-- in-flight: in-flight loss: s <= b + 3 × 50 @step  (7 columns)
def t3_goal : Goal := ⟨[.var 0, .var 1, .var 2, .var 3, .var 4, .term (.min (.var 4) (.const 50)), .term (.ite (.and (.eq (.var 0) (.const 1)) (.lt (.const 0) (.var 3))) (.add (.var 1) (.min (.var 4) (.const 50))) (.var 1))],
  [.or (.eq (.var 0) (.const 0)) (.eq (.var 0) (.const 1)), .le (.var 1) (.add (.var 2) (.const 150)), .le (.add (.var 1) (.mul 50 (.var 3))) (.add (.var 2) (.const 150)), .not (.le (.ite (.and (.eq (.var 0) (.const 1)) (.lt (.const 0) (.var 3))) (.add (.var 1) (.min (.var 4) (.const 50))) (.var 1)) (.add (.var 2) (.const 150)))]⟩
def t3_tree : Tree :=
  .split (sp [(0, 1)] (-1))
  (.split (sp [(0, (-1))] 1)
  (.split (sp [(3, (-1))] 1)
  (.split (sp [(4, 1)] (-50))
  (.leafAt [((sp [(3, (-1))] 1), .atom 1), ((sp [(4, 1)] (-50)), .atom 0), ((sp [(1, 1), (2, (-1)), (3, 50)] (-150)), .fact 2), ((sp [(1, (-1)), (2, 1), (4, (-1))] 151), .fact 3)] [.input 0, .input 1, .input 2, .input 3, .combine 2 0 1 50, .combine 1 3 1 1, .combine 4 5 1 1] [] [])
  (.leafAt [((sp [(3, (-1))] 1), .atom 1), ((sp [(1, 1), (2, (-1)), (3, 50)] (-150)), .fact 2), ((sp [(1, (-1)), (2, 1)] 101), .fact 3)] [.input 0, .input 1, .input 2, .combine 1 0 1 50, .combine 3 2 1 1] [] []))
  (.leafAt [((sp [(1, 1), (2, (-1))] (-150)), .fact 1), ((sp [(1, (-1)), (2, 1)] 151), .fact 3)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(1, 1), (2, (-1))] (-150)), .fact 1), ((sp [(1, (-1)), (2, 1)] 151), .fact 3)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(0, (-1))] 2), .atom 0), ((sp [(0, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
theorem t3 : ∀ env maps, ¬ ∀ c ∈ t3_goal.hyps, evalC env maps c = true :=
  sound t3_goal t3_tree (by decide +kernel)

-- in-flight: s + 50p <= b + 150 @start  (1 columns)
def t4_goal : Goal := ⟨[.var 0],
  [.not (.le (.add (.const 0) (.mul 50 (.const 0))) (.add (.var 0) (.const 150)))]⟩
def t4_tree : Tree :=
  .leafAt [((sp [(0, 1)] 151), .fact 0), ((sp [(0, (-1))] 0), .nat 0)] [.input 0, .input 1, .combine 0 1 1 1] [] []
theorem t4 : ∀ env maps, ¬ ∀ c ∈ t4_goal.hyps, evalC env maps c = true :=
  sound t4_goal t4_tree (by decide +kernel)

-- in-flight: s + 50p <= b + 150 @step  (11 columns)
def t5_goal : Goal := ⟨[.var 0, .var 1, .var 2, .var 3, .var 4, .term (.min (.var 4) (.const 50)), .term (.ite (.and (.eq (.var 0) (.const 1)) (.lt (.const 0) (.var 3))) (.add (.var 1) (.min (.var 4) (.const 50))) (.var 1)), .term (.ite (.and (.lt (.var 1) (.var 2)) (.lt (.var 3) (.const 3))) (.add (.var 3) (.const 1)) (.var 3)), .term (.sub (.var 3) (.const 1)), .term (.ite (.lt (.const 0) (.var 3)) (.sub (.var 3) (.const 1)) (.var 3)), .term (.ite (.eq (.var 0) (.const 1)) (.ite (.lt (.const 0) (.var 3)) (.sub (.var 3) (.const 1)) (.var 3)) (.ite (.and (.lt (.var 1) (.var 2)) (.lt (.var 3) (.const 3))) (.add (.var 3) (.const 1)) (.var 3)))],
  [.or (.eq (.var 0) (.const 0)) (.eq (.var 0) (.const 1)), .le (.var 1) (.add (.var 2) (.const 150)), .le (.add (.var 1) (.mul 50 (.var 3))) (.add (.var 2) (.const 150)), .not (.le (.add (.ite (.and (.eq (.var 0) (.const 1)) (.lt (.const 0) (.var 3))) (.add (.var 1) (.min (.var 4) (.const 50))) (.var 1)) (.mul 50 (.ite (.eq (.var 0) (.const 1)) (.ite (.lt (.const 0) (.var 3)) (.sub (.var 3) (.const 1)) (.var 3)) (.ite (.and (.lt (.var 1) (.var 2)) (.lt (.var 3) (.const 3))) (.add (.var 3) (.const 1)) (.var 3))))) (.add (.var 2) (.const 150)))]⟩
def t5_tree : Tree :=
  .split (sp [(0, 1)] (-1))
  (.split (sp [(0, (-1))] 1)
  (.split (sp [(3, (-1))] 1)
  (.split (sp [(4, 1)] (-50))
  (.leafAt [((sp [(4, 1)] (-50)), .atom 0), ((sp [(1, 1), (2, (-1)), (3, 50)] (-150)), .fact 2), ((sp [(1, (-1)), (2, 1), (3, (-50)), (4, (-1))] 201), .fact 3)] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 3 1 1 1] [] [])
  (.leafAt [((sp [(1, 1), (2, (-1)), (3, 50)] (-150)), .fact 2), ((sp [(1, (-1)), (2, 1), (3, (-50))] 151), .fact 3)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(3, 1)] 0), .atom 0), ((sp [(1, 1), (2, (-1))] (-150)), .fact 1), ((sp [(1, (-1)), (2, 1), (3, (-50))] 151), .fact 3)] [.input 0, .input 1, .input 2, .combine 2 0 1 50, .combine 3 1 1 1] [] []))
  (.split (sp [(1, 1), (2, (-1))] 1)
  (.split (sp [(3, 1)] (-2))
  (.leafAt [((sp [(1, 1), (2, (-1))] 1), .atom 1), ((sp [(3, 1)] (-2)), .atom 0), ((sp [(1, (-1)), (2, 1), (3, (-50))] 101), .fact 3)] [.input 0, .input 1, .input 2, .combine 2 0 1 1, .cut 3 50 [(3, (-1))] 3, .combine 1 4 1 1] [] [])
  (.leafAt [((sp [(1, 1), (2, (-1)), (3, 50)] (-150)), .fact 2), ((sp [(1, (-1)), (2, 1), (3, (-50))] 151), .fact 3)] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leafAt [((sp [(1, 1), (2, (-1)), (3, 50)] (-150)), .fact 2), ((sp [(1, (-1)), (2, 1), (3, (-50))] 151), .fact 3)] [.input 0, .input 1, .combine 0 1 1 1] [] [])))
  (.leafAt [((sp [(0, (-1))] 2), .atom 0), ((sp [(0, 1)] 0), .fact 0)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
theorem t5 : ∀ env maps, ¬ ∀ c ∈ t5_goal.hyps, evalC env maps c = true :=
  sound t5_goal t5_tree (by decide +kernel)

-- products: x <= x·x  (4 columns)
def t6_goal : Goal := ⟨[.var 0, .mono [0, 0], .mono [0, 0, 0], .mono [0, 0, 0, 0]],
  [.not (.le (.var 0) (.prod (.var 0) (.var 0)))]⟩
def t6_tree : Tree :=
  .leafAt [((sp [(0, (-1)), (1, 1)] 1), .fact 0), ((sp [(1, (-1))] 0), .nat 1), ((sp [(0, (-1))] 0), .nat 0)] [.input 0, .input 5, .input 7, .combine 1 0 1 1, .combine 3 2 1 1] [] [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)]
theorem t6 : ∀ env maps, ¬ ∀ c ∈ t6_goal.hyps, evalC env maps c = true :=
  sound t6_goal t6_tree (by decide +kernel)

-- TAMPERED: budget rule: bounded_loss: s <= b + m @step, the first leaf's derivation without its last step. Lean computes the check to false.
def tampered1_goal : Goal := ⟨[.var 0, .var 1, .var 2, .var 3, .term (.min (.var 3) (.var 2)), .term (.ite (.lt (.var 0) (.var 1)) (.add (.var 0) (.min (.var 3) (.var 2))) (.var 0))],
  [.le (.var 0) (.add (.var 1) (.var 2)), .not (.le (.ite (.lt (.var 0) (.var 1)) (.add (.var 0) (.min (.var 3) (.var 2))) (.var 0)) (.add (.var 1) (.var 2)))]⟩
def tampered1_tree : Tree :=
  .split (sp [(0, 1), (1, (-1))] 1)
  (.split (sp [(2, (-1)), (3, 1)] 0)
  (.leafAt [((sp [(0, 1), (1, (-1))] 1), .atom 1), ((sp [(2, (-1)), (3, 1)] 0), .atom 0), ((sp [(0, (-1)), (1, 1), (2, 1), (3, (-1))] 1), .fact 1)] [.input 0, .input 1, .input 2, .combine 2 0 1 1] [] [])
  (.leafAt [((sp [(0, 1), (1, (-1))] 1), .atom 1), ((sp [(0, (-1)), (1, 1)] 1), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(0, 1), (1, (-1)), (2, (-1))] 0), .fact 0), ((sp [(0, (-1)), (1, 1), (2, 1)] 1), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
example : checkGoal tampered1_goal tampered1_tree = false := by decide +kernel

-- TAMPERED: the x <= x·x tree offered for x·x <= x. Lean computes the check to false.
def tampered1002_goal : Goal := ⟨[.var 0, .mono [0, 0], .mono [0, 0, 0], .mono [0, 0, 0, 0]],
  [.not (.le (.prod (.var 0) (.var 0)) (.var 0))]⟩
def tampered1002_tree : Tree :=
  .leafAt [((sp [(0, 1), (1, (-1))] 1), .fact 0), ((sp [(0, (-1))] 0), .nat 0), ((sp [(1, (-1))] 0), .nat 1)] [.input 0, .input 5, .input 7, .combine 1 0 1 1, .combine 3 2 1 1] [] [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)]
example : checkGoal tampered1002_goal tampered1002_tree = false := by decide +kernel

-- TAMPERED: budget rule: the bounded_loss tree offered for s <= b. Lean computes the check to false.
def tampered1001_goal : Goal := ⟨[.var 0, .var 1, .var 2, .var 3, .term (.min (.var 2) (.var 3)), .term (.ite (.lt (.var 0) (.var 1)) (.add (.var 0) (.min (.var 2) (.var 3))) (.var 0))],
  [.le (.var 0) (.var 1), .not (.le (.ite (.lt (.var 0) (.var 1)) (.add (.var 0) (.min (.var 2) (.var 3))) (.var 0)) (.var 1))]⟩
def tampered1001_tree : Tree :=
  .split (sp [(0, 1), (1, (-1))] 1)
  (.split (sp [(2, 1), (3, (-1))] 0)
  (.leafAt [((sp [(0, 1), (1, (-1))] 1), .atom 1), ((sp [(2, 1), (3, (-1))] 0), .atom 0), ((sp [(0, (-1)), (1, 1), (2, (-1))] 1), .fact 1)] [.input 0, .input 1, .input 2, .combine 2 0 1 1, .combine 1 3 1 1] [] [])
  (.leafAt [((sp [(0, 1), (1, (-1))] 1), .atom 1), ((sp [(0, (-1)), (1, 1), (3, (-1))] 1), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leafAt [((sp [(0, 1), (1, (-1))] 0), .fact 0), ((sp [(0, (-1)), (1, 1)] 1), .fact 1)] [.input 0, .input 1, .combine 0 1 1 1] [] [])
example : checkGoal tampered1001_goal tampered1001_tree = false := by decide +kernel

#print axioms t0
#print axioms t6
#print axioms bounded_loss
#print axioms inflight_loss
#print axioms gcd_halts
#print axioms grid_halts
#print axioms leaves_eq_nodes_succ
#print axioms rollup_laws
#print axioms day_cap
#print axioms loss_per_request
#print axioms rollupM_laws
#print axioms peracct_laws
#print axioms fpolicy_laws
#print axioms fadmit_laws
#print axioms flight_complete_holds
#print axioms flight_admit_holds
#print axioms admit_grant_holds
#print axioms fadmit_grant_holds
#print axioms refines_laws
#print axioms refines_step0_holds
#print axioms interleaved_laws
#print axioms interleaved_step0_holds
#print axioms interleaved_step1_holds
#print axioms twophase_laws
#print axioms twophase_step0_holds
#print axioms escrow_laws
#print axioms escrow_step0_holds
#print axioms pooltotal_laws
