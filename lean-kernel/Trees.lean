import Progress
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
  ([.var 0, .var 1, .var 2, .var 3], .leaf [⟨[1, 1], 1⟩, ⟨[(-1)], 0⟩, ⟨[0, (-1)], 0⟩] [.input 0, .input 1, .input 2, .combine 0 1 1 1, .combine 3 2 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3], .split ⟨[(-1), 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 1], 0⟩
  (.leaf [⟨[(-1), 0, 0, 1], 1⟩, ⟨[0, (-1), 1], 0⟩, ⟨[1, 1, (-1), (-1)], 1⟩] [.input 0, .input 1, .input 2, .combine 2 0 1 1, .combine 1 3 1 1] [] [])
  (.leaf [⟨[(-1), 0, 0, 1], 1⟩, ⟨[1, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[(-1), (-1), 0, 1], 0⟩, ⟨[1, 1, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))]
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
  ([.var 0, .var 1, .var 2, .var 3, .var 4], .leaf [⟨[1], 151⟩, ⟨[(-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4], .split ⟨[0, 0, 1], 0⟩
  (.leaf [⟨[(-1), 0, 0, 1], (-150)⟩, ⟨[1, 0, 0, (-1)], 151⟩] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.split ⟨[0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, (-1)], 1⟩
  (.split ⟨[0, 1], (-50)⟩
  (.leaf [⟨[0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 1], (-50)⟩, ⟨[(-1), 0, 0, 1, 50], (-150)⟩, ⟨[1, (-1), 0, (-1)], 151⟩] [.input 0, .input 1, .input 2, .input 3, .combine 2 0 1 50, .combine 1 3 1 1, .combine 4 5 1 1] [] [])
  (.leaf [⟨[0, 0, 0, 0, (-1)], 1⟩, ⟨[(-1), 0, 0, 1, 50], (-150)⟩, ⟨[1, 0, 0, (-1)], 101⟩] [.input 0, .input 1, .input 2, .combine 1 0 1 50, .combine 3 2 1 1] [] []))
  (.leaf [⟨[(-1), 0, 0, 1], (-150)⟩, ⟨[1, 0, 0, (-1)], 151⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[], 1⟩] [.input 0] [] [])))), (.le (.add (.var 3) (.mul 50 (.var 4))) (.add (.var 0) (.const 150)),
  ([.var 0, .var 1, .var 2, .var 3, .var 4], .leaf [⟨[1], 151⟩, ⟨[(-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4], .split ⟨[0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 1], 1⟩
  (.split ⟨[0, 0, 0, 0, 1], (-2)⟩
  (.leaf [⟨[(-1), 0, 0, 1], 1⟩, ⟨[0, 0, 0, 0, 1], (-2)⟩, ⟨[1, 0, 0, (-1), (-50)], 101⟩] [.input 0, .input 1, .input 2, .combine 2 0 1 1, .cut 3 50 [0, 0, 0, 0, (-1)] 3, .combine 1 4 1 1] [] [])
  (.leaf [⟨[(-1), 0, 0, 1, 50], (-150)⟩, ⟨[1, 0, 0, (-1), (-50)], 151⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[(-1), 0, 0, 1, 50], (-150)⟩, ⟨[1, 0, 0, (-1), (-50)], 151⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, (-1)], 1⟩
  (.split ⟨[0, 1], (-50)⟩
  (.leaf [⟨[0, 1], (-50)⟩, ⟨[(-1), 0, 0, 1, 50], (-150)⟩, ⟨[1, (-1), 0, (-1), (-50)], 201⟩] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 3 1 1 1] [] [])
  (.leaf [⟨[(-1), 0, 0, 1, 50], (-150)⟩, ⟨[1, 0, 0, (-1), (-50)], 151⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[0, 0, 0, 0, 1], 0⟩, ⟨[(-1), 0, 0, 1], (-150)⟩, ⟨[1, 0, 0, (-1), (-50)], 151⟩] [.input 0, .input 1, .input 2, .combine 2 0 1 50, .combine 3 1 1 1] [] []))
  (.leaf [⟨[], 1⟩] [.input 0] [] []))))]
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
  ([.var 0, .var 1, .var 2, .var 3], .leaf [⟨[], 1⟩] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .mono [0, 3]], .split ⟨[(-1), 1], 0⟩
  (.leaf [⟨[(-1), 1], 0⟩, ⟨[0, 0, 1, 0, (-1)], 0⟩, ⟨[1, (-1), (-1), 0, 1], 1⟩] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 1 3 1 1] [] [])
  (.leaf [⟨[0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, (-1), 0, 1], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))]
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

-- gcd by subtraction: halts with ranks 1, invariants a >= 1; b >= 1  (variables 0 A, 1 B, 2 a, 3 b)
def gcd_loop : Loop := ⟨[],
  [(2, .var 0), (3, .var 1)],
  [(2, .ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)), (3, .ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3))],
  .not (.eq (.var 2) (.var 3)),
  .and (.le (.const 1) (.var 0)) (.le (.const 1) (.var 1)),
  .le (.const 0) (.const 0)⟩
def gcd_proof : LoopProof := ⟨[(.le (.const 1) (.var 2),
  ([.var 0, .var 1, .var 2, .var 3], .leaf [⟨[(-1)], 1⟩, ⟨[1], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3], .split ⟨[0, 0, 1, (-1)], 0⟩
  (.leaf [⟨[0, 0, (-1)], 1⟩, ⟨[0, 0, 1], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.split ⟨[0, 0, (-1), 1], 0⟩
  (.leaf [⟨[], 1⟩] [.input 0] [] [])
  (.leaf [⟨[0, 0, (-1), 1], 1⟩, ⟨[0, 0, 1, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] [])))), (.le (.const 1) (.var 3),
  ([.var 0, .var 1, .var 2, .var 3], .leaf [⟨[0, (-1)], 1⟩, ⟨[0, 1], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3], .split ⟨[0, 0, 1, (-1)], 0⟩
  (.split ⟨[0, 0, (-1), 1], 0⟩
  (.leaf [⟨[], 1⟩] [.input 0] [] [])
  (.leaf [⟨[], 1⟩] [.input 0] [] []))
  (.split ⟨[0, 0, 1, (-1)], 1⟩
  (.leaf [⟨[0, 0, (-1), 1], 1⟩, ⟨[0, 0, 1, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leaf [⟨[0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 1], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))))],
  [.add (.var 2) (.var 3)],
  ([.var 0, .var 1, .var 2, .var 3], .split ⟨[0, 0, 1, (-1)], 0⟩
  (.split ⟨[0, 0, (-1), 1], 0⟩
  (.leaf [⟨[], 1⟩] [.input 0] [] [])
  (.leaf [⟨[0, 0, (-1)], 1⟩, ⟨[0, 0, 1], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, (-1), 1], 0⟩
  (.leaf [⟨[0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 1], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leaf [⟨[0, 0, (-1), 1], 1⟩, ⟨[0, 0, 1, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] [])))⟩
theorem gcd_halts : ∀ maps ρ0, evalC ρ0 maps gcd_loop.pre = true →
    ¬ ∃ f : Nat → Nat → Nat, f 0 = applyS gcd_loop.init ρ0 maps ∧ ∀ n, Turn gcd_loop maps (f n) (f (n + 1)) :=
  loop_sound gcd_loop gcd_proof (by decide +kernel)
-- TAMPERED: the gcd proof without the precondition A, B >= 1. Lean computes the check to false.
def gcd_tampered : Loop := ⟨[],
  [(2, .var 0), (3, .var 1)],
  [(2, .ite (.lt (.var 3) (.var 2)) (.sub (.var 2) (.var 3)) (.var 2)), (3, .ite (.lt (.var 2) (.var 3)) (.sub (.var 3) (.var 2)) (.var 3))],
  .not (.eq (.var 2) (.var 3)),
  .le (.const 0) (.const 0),
  .le (.const 0) (.const 0)⟩
example : checkLoop gcd_tampered gcd_proof = false := by decide +kernel

-- pagination: halts with ranks 1  (variables 0 total, 1 page, 2 cur)
def pages_loop : Loop := ⟨[1],
  [(2, .const 0)],
  [(2, .add (.var 2) (.min (.var 1) (.sub (.var 0) (.var 2))))],
  .lt (.var 2) (.var 0),
  .le (.const 0) (.const 0),
  .le (.const 1) (.var 1)⟩
def pages_proof : LoopProof := ⟨[],
  [.sub (.var 0) (.var 2)],
  ([.var 0, .var 1, .var 2], .split ⟨[(-1), 0, 1], 0⟩
  (.split ⟨[(-1), 1, 1], 0⟩
  (.leaf [⟨[0, (-1)], 1⟩, ⟨[0, 1], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leaf [⟨[(-1), 0, 1], 1⟩, ⟨[1, 0, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[1, 0, (-1)], 1⟩, ⟨[(-1), 0, 1], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))⟩
theorem pages_halts : ∀ maps ρ0, evalC ρ0 maps pages_loop.pre = true →
    ¬ ∃ f : Nat → Nat → Nat, f 0 = applyS pages_loop.init ρ0 maps ∧ ∀ n, Turn pages_loop maps (f n) (f (n + 1)) :=
  loop_sound pages_loop pages_proof (by decide +kernel)
-- TAMPERED: the pagination proof when a page may be empty. Lean computes the check to false.
def pages_tampered : Loop := ⟨[1],
  [(2, .const 0)],
  [(2, .add (.var 2) (.min (.var 1) (.sub (.var 0) (.var 2))))],
  .lt (.var 2) (.var 0),
  .le (.const 0) (.const 0),
  .le (.const 0) (.var 1)⟩
example : checkLoop pages_tampered pages_proof = false := by decide +kernel

-- retry: halts with ranks 1  (variables 0 budget, 1 wait, 2 spent, 3 tries)
def retry_loop : Loop := ⟨[1],
  [(2, .const 0), (3, .const 0)],
  [(2, .add (.var 2) (.max (.const 1) (.var 1))), (3, .add (.var 3) (.const 1))],
  .lt (.var 2) (.var 0),
  .le (.const 0) (.const 0),
  .le (.const 0) (.const 0)⟩
def retry_proof : LoopProof := ⟨[],
  [.sub (.var 0) (.var 2)],
  ([.var 0, .var 1, .var 2, .var 3], .split ⟨[0, (-1)], 1⟩
  (.split ⟨[(-1), 1, 1], 0⟩
  (.split ⟨[(-1), 0, 1], 0⟩
  (.leaf [⟨[], 1⟩] [.input 0] [] [])
  (.leaf [⟨[1, 0, (-1)], 1⟩, ⟨[(-1), 0, 1], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[(-1), 0, 1], 0⟩
  (.leaf [⟨[(-1), 0, 1], 1⟩, ⟨[1, 0, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leaf [⟨[1, 0, (-1)], 1⟩, ⟨[(-1), 0, 1], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] [])))
  (.split ⟨[(-1), 0, 1], 1⟩
  (.split ⟨[(-1), 0, 1], 0⟩
  (.leaf [⟨[], 1⟩] [.input 0] [] [])
  (.leaf [⟨[(-1), 0, 1], 1⟩, ⟨[1, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[1, 0, (-1)], 0⟩, ⟨[(-1), 0, 1], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] [])))⟩
theorem retry_halts : ∀ maps ρ0, evalC ρ0 maps retry_loop.pre = true →
    ¬ ∃ f : Nat → Nat → Nat, f 0 = applyS retry_loop.init ρ0 maps ∧ ∀ n, Turn retry_loop maps (f n) (f (n + 1)) :=
  loop_sound retry_loop retry_proof (by decide +kernel)

-- every cell of an n × m grid: halts with ranks 2  (variables 0 n, 1 m, 2 i, 3 j)
def grid_loop : Loop := ⟨[],
  [(2, .const 0), (3, .const 0)],
  [(2, .ite (.lt (.var 3) (.var 1)) (.var 2) (.add (.var 2) (.const 1))), (3, .ite (.lt (.var 3) (.var 1)) (.add (.var 3) (.const 1)) (.const 0))],
  .lt (.var 2) (.var 0),
  .le (.const 0) (.const 0),
  .le (.const 0) (.const 0)⟩
def grid_proof : LoopProof := ⟨[],
  [.sub (.var 0) (.var 2), .sub (.var 1) (.var 3)],
  ([.var 0, .var 1, .var 2, .var 3], .split ⟨[0, (-1), 0, 1], 1⟩
  (.split ⟨[(-1), 0, 1], 0⟩
  (.split ⟨[0, (-1), 0, 1], 0⟩
  (.leaf [⟨[], 1⟩] [.input 0] [] [])
  (.leaf [⟨[0, (-1), 0, 1], 1⟩, ⟨[0, 1, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[1, 0, (-1)], 1⟩, ⟨[(-1), 0, 1], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.split ⟨[(-1), 0, 1], 1⟩
  (.split ⟨[(-1), 0, 1], 0⟩
  (.leaf [⟨[], 1⟩] [.input 0] [] [])
  (.leaf [⟨[(-1), 0, 1], 1⟩, ⟨[1, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[1, 0, (-1)], 0⟩, ⟨[(-1), 0, 1], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] [])))⟩
theorem grid_halts : ∀ maps ρ0, evalC ρ0 maps grid_loop.pre = true →
    ¬ ∃ f : Nat → Nat → Nat, f 0 = applyS grid_loop.init ρ0 maps ∧ ∀ n, Turn grid_loop maps (f n) (f (n + 1)) :=
  loop_sound grid_loop grid_proof (by decide +kernel)

-- TAMPERED: a rank (w ∸ x) that reads the turn's input w: its rank goal checks, yet the loop runs forever when every
-- turn sends w = x + 1. Lean's check refuses ranks over inputs and computes to false (kernel.ts now refuses them too).
def forever_loop : Loop := ⟨[0], [(1, .const 0)], [(1, .add (.var 1) (.const 1))], .lt (.var 1) (.var 0), .le (.const 0) (.const 0), .le (.const 0) (.const 0)⟩
def forever_proof : LoopProof := ⟨[], [.sub (.var 0) (.var 1)], ([.var 0, .var 1], .split ⟨[(-1), 1], 1⟩
  (.split ⟨[(-1), 1], 0⟩
  (.leaf [⟨[], 1⟩] [.input 0] [] [])
  (.leaf [⟨[(-1), 1], 1⟩, ⟨[1, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[1, (-1)], 0⟩, ⟨[(-1), 1], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))⟩
example : checkLoop forever_loop forever_proof = false := by decide +kernel
-- Without that check the rank goal alone would pass:
example : checkGoal ⟨forever_proof.rank.1, rankGoal forever_loop [] forever_proof.ranks⟩ forever_proof.rank.2 = true := by decide +kernel

-- shape: leaves = nodes + 1; height <= nodes; height < leaves  (variables 0 leaves, 1 nodes, 2 height, 3 l_leaves, 4 l_nodes, 5 l_height, 6 r_leaves, 7 r_nodes, 8 r_height)
def shape_fold : Fold := ⟨[],
  [(0, 3, 6), (1, 4, 7), (2, 5, 8)],
  [(0, .const 1), (1, .const 0), (2, .const 0)],
  [(0, .add (.var 3) (.var 6)), (1, .add (.add (.var 4) (.var 7)) (.const 1)), (2, .add (.max (.var 5) (.var 8)) (.const 1))],
  .le (.const 0) (.const 0),
  .le (.const 0) (.const 0)⟩
def shape_proof : FoldProof := [(.eq (.var 0) (.add (.var 1) (.const 1)),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8], .leaf [⟨[], 1⟩] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8], .split ⟨[0, 0, 0, 1, (-1), 0, 1, (-1)], (-2)⟩
  (.leaf [⟨[0, 0, 0, (-1), 1], 1⟩, ⟨[0, 0, 0, 0, 0, 0, (-1), 1], 1⟩, ⟨[0, 0, 0, 1, (-1), 0, 1, (-1)], (-1)⟩] [.input 0, .input 1, .input 2, .combine 2 0 1 1, .combine 3 1 1 1] [] [])
  (.leaf [⟨[0, 0, 0, (-1), 1, 0, (-1), 1], 3⟩, ⟨[0, 0, 0, 1, (-1)], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 1, (-1)], (-1)⟩] [.input 0, .input 1, .input 2, .combine 0 1 1 1, .combine 3 2 1 1] [] []))), (.le (.var 2) (.var 1),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8], .leaf [⟨[], 1⟩] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8], .split ⟨[0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩, ⟨[0, 0, 0, 0, 1, 0, 0, 1, (-1)], 1⟩, ⟨[0, 0, 0, 0, (-1)], 0⟩] [.input 0, .input 1, .input 2, .combine 0 1 1 1, .combine 3 2 1 1] [] [])
  (.leaf [⟨[0, 0, 0, 0, (-1), 1], 0⟩, ⟨[0, 0, 0, 0, 1, (-1), 0, 1], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩] [.input 0, .input 1, .input 2, .combine 0 1 1 1, .combine 3 2 1 1] [] []))), (.lt (.var 2) (.var 0),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8], .leaf [⟨[], 1⟩] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8], .split ⟨[0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩
  (.leaf [⟨[0, 0, 0, (-1), 1], 1⟩, ⟨[0, 0, 0, 0, 0, 0, (-1), 1], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩, ⟨[0, 0, 0, 1, 0, 0, 1, 0, (-1)], (-1)⟩, ⟨[0, 0, 0, 0, (-1)], 0⟩] [.input 0, .input 1, .input 2, .input 3, .input 4, .combine 3 0 1 1, .combine 5 1 1 1, .combine 2 6 1 1, .combine 7 4 1 1] [] [])
  (.leaf [⟨[0, 0, 0, (-1), 1], 1⟩, ⟨[0, 0, 0, 0, 0, 0, (-1), 1], 1⟩, ⟨[0, 0, 0, 0, (-1), 1], 0⟩, ⟨[0, 0, 0, 1, 0, (-1), 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩] [.input 0, .input 1, .input 2, .input 3, .input 4, .combine 3 0 1 1, .combine 5 1 1 1, .combine 2 6 1 1, .combine 7 4 1 1] [] [])))]
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
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6], .split ⟨[1], (-50)⟩
  (.leaf [⟨[], 1⟩] [.input 0] [] [])
  (.leaf [⟨[], 1⟩] [.input 0] [] [])),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6], .leaf [⟨[0, 0, 0, 1, (-50)], 0⟩, ⟨[0, 0, 0, 0, 0, 1, (-50)], 0⟩, ⟨[0, 0, 0, (-1), 50, (-1), 50], 1⟩] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 1 3 1 1] [] []))]
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
def admit_proof : List MEntry := [⟨⟨.le (.get 0 (.var 8)) (.const 1), some 8⟩, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10], .leaf [⟨[], 1⟩] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .cell 0 ⟨[0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, (-1), 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 1, 0, 0, 0, 0, 0, (-1)], 0⟩
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 4 5 1 1] [(11, 15), (16, 20), (21, 25), (26, 30)] [])
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 0, (-1), 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 1, 0, 0, 0, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(11, 15), (16, 20), (21, 25), (26, 30)] [])
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 1 0 1 1] [(11, 15), (16, 20), (21, 25), (26, 30)] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 1 0 1 1] [(11, 15), (16, 20), (21, 25), (26, 30)] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 1 0 1 1] [(11, 15), (16, 20), (21, 25), (26, 30)] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 1 0 1 1] [(11, 15), (16, 20), (21, 25), (26, 30)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [(11, 15), (16, 20), (21, 25), (26, 30)] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩, ⟨⟨.le (.get 1 (.var 8)) (.var 0), some 8⟩, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10], .leaf [⟨[1], 1⟩, ⟨[(-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .cell 0 ⟨[0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, (-1), 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, (-1)], 0⟩
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(12, 15), (17, 20), (22, 25), (27, 30)] [])
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 0, 0, (-1), 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(12, 15), (17, 20), (22, 25), (27, 30)] [])
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(12, 15), (17, 20), (22, 25), (27, 30)] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(12, 15), (17, 20), (22, 25), (27, 30)] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [(12, 15), (17, 20), (22, 25), (27, 30)] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(12, 15), (17, 20), (22, 25), (27, 30)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [(12, 15), (17, 20), (22, 25), (27, 30)] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩, ⟨⟨.le (.get 2 (.var 8)) (.var 1), some 8⟩, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10], .leaf [⟨[0, 1], 1⟩, ⟨[0, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .cell 0 ⟨[0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, (-1), 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 1, 0, 0, 0, (-1)], 0⟩
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(13, 15), (18, 20), (23, 25), (28, 30)] [])
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 0, 0, 0, (-1), 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 1, 0, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(13, 15), (18, 20), (23, 25), (28, 30)] [])
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(13, 15), (18, 20), (23, 25), (28, 30)] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [(13, 15), (18, 20), (23, 25), (28, 30)] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(13, 15), (18, 20), (23, 25), (28, 30)] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(13, 15), (18, 20), (23, 25), (28, 30)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [(13, 15), (18, 20), (23, 25), (28, 30)] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩, ⟨⟨.le (.get 3 (.var 8)) (.var 2), some 8⟩, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10], .leaf [⟨[0, 0, 1], 1⟩, ⟨[0, 0, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .cell 0 ⟨[0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(14, 15), (19, 20), (24, 25), (29, 30)] [])
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(14, 15), (19, 20), (24, 25), (29, 30)] [])
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [(14, 15), (19, 20), (24, 25), (29, 30)] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(14, 15), (19, 20), (24, 25), (29, 30)] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(14, 15), (19, 20), (24, 25), (29, 30)] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(14, 15), (19, 20), (24, 25), (29, 30)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [(14, 15), (19, 20), (24, 25), (29, 30)] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩]
theorem admit_check : checkFMMachine admit_machine admit_proof = true := by decide +kernel
theorem admit_laws : ∀ ρ M, FMReach admit_machine ρ M → ∀ e ∈ admit_proof, e.law.Holds ρ M :=
  fmmachine_sound admit_machine admit_proof admit_check
-- the caps rule's day cap in plain Lean: in every reachable state, every Day count is at most d (variable 0; Day is map 1).
theorem day_cap (ρ : Nat → Nat) (M : Nat → Nat → Nat) (h : FMReach admit_machine ρ M) (k : Nat) : M 1 k ≤ ρ 0 := by
  have := admit_laws ρ M h _ (List.mem_cons_of_mem _ List.mem_cons_self) k
  simpa [evalC, evalE, upd] using this
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
  ([.var 0, .var 1, .var 2, .var 3, .var 4], .leaf [⟨[1, 1], 1⟩, ⟨[(-1)], 0⟩, ⟨[0, (-1)], 0⟩] [.input 0, .input 1, .input 2, .combine 0 1 1 1, .combine 3 2 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4], .split ⟨[(-1), 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 1], 0⟩
  (.leaf [⟨[(-1), 0, 0, 1], 1⟩, ⟨[0, (-1), 1], 0⟩, ⟨[1, 1, (-1), (-1)], 1⟩] [.input 0, .input 1, .input 2, .combine 2 0 1 1, .combine 1 3 1 1] [] [])
  (.leaf [⟨[(-1), 0, 0, 1], 1⟩, ⟨[1, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[(-1), (-1), 0, 1], 0⟩, ⟨[1, 1, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))]
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
def fadmit_proof : List MEntry := [⟨⟨.le (.get 0 (.var 8)) (.const 1), some 8⟩, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11], .leaf [⟨[], 1⟩] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .cell 0 ⟨[0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, (-1), 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 1, 0, 0, 0, 0, 0, (-1)], 0⟩
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 4 5 1 1] [(12, 16), (17, 21), (22, 26), (27, 31)] [])
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 0, (-1), 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 1, 0, 0, 0, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(12, 16), (17, 21), (22, 26), (27, 31)] [])
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 1 0 1 1] [(12, 16), (17, 21), (22, 26), (27, 31)] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 1 0 1 1] [(12, 16), (17, 21), (22, 26), (27, 31)] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 1 0 1 1] [(12, 16), (17, 21), (22, 26), (27, 31)] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 1 0 1 1] [(12, 16), (17, 21), (22, 26), (27, 31)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [(12, 16), (17, 21), (22, 26), (27, 31)] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩, ⟨⟨.le (.get 1 (.var 8)) (.var 0), some 8⟩, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11], .leaf [⟨[1], 1⟩, ⟨[(-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .cell 0 ⟨[0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, (-1), 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, (-1)], 0⟩
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(13, 16), (18, 21), (23, 26), (28, 31)] [])
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 0, 0, (-1), 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(13, 16), (18, 21), (23, 26), (28, 31)] [])
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(13, 16), (18, 21), (23, 26), (28, 31)] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(13, 16), (18, 21), (23, 26), (28, 31)] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [(13, 16), (18, 21), (23, 26), (28, 31)] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(13, 16), (18, 21), (23, 26), (28, 31)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [(13, 16), (18, 21), (23, 26), (28, 31)] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩, ⟨⟨.le (.get 2 (.var 8)) (.var 1), some 8⟩, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11], .leaf [⟨[0, 1], 1⟩, ⟨[0, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .cell 0 ⟨[0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, (-1), 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 1, 0, 0, 0, (-1)], 0⟩
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(14, 16), (19, 21), (24, 26), (29, 31)] [])
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 0, 0, 0, (-1), 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 1, 0, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(14, 16), (19, 21), (24, 26), (29, 31)] [])
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(14, 16), (19, 21), (24, 26), (29, 31)] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [(14, 16), (19, 21), (24, 26), (29, 31)] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(14, 16), (19, 21), (24, 26), (29, 31)] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(14, 16), (19, 21), (24, 26), (29, 31)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [(14, 16), (19, 21), (24, 26), (29, 31)] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩, ⟨⟨.le (.get 3 (.var 8)) (.var 2), some 8⟩, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11], .leaf [⟨[0, 0, 1], 1⟩, ⟨[0, 0, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .cell 0 ⟨[0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(15, 16), (20, 21), (25, 26), (30, 31)] [])
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(15, 16), (20, 21), (25, 26), (30, 31)] [])
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [(15, 16), (20, 21), (25, 26), (30, 31)] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(15, 16), (20, 21), (25, 26), (30, 31)] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(15, 16), (20, 21), (25, 26), (30, 31)] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(15, 16), (20, 21), (25, 26), (30, 31)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [(15, 16), (20, 21), (25, 26), (30, 31)] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩]
theorem fadmit_check : checkFMMachine fadmit_machine fadmit_proof = true := by decide +kernel
theorem fadmit_laws : ∀ ρ M, FMReach fadmit_machine ρ M → ∀ e ∈ fadmit_proof, e.law.Holds ρ M :=
  fmmachine_sound fadmit_machine fadmit_proof fadmit_check
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

-- in-flight requests: in-flight loss: s <= b + 3 × 50; s + 50p <= b + 150  (variables 0 b, 1 t, 2 done, 3 s, 4 p, 5 #, 6 s', 7 p'; maps )
def pflight_machine : FMMachine := ⟨⟨[1, 2],
  [(3, .const 0), (4, .const 0)],
  [],
  [(3, .ite (.and (.eq (.var 2) (.const 1)) (.lt (.const 0) (.var 4))) (.add (.var 3) (.min (.var 1) (.const 50))) (.var 3)), (4, .ite (.eq (.var 2) (.const 1)) (.ite (.lt (.const 0) (.var 4)) (.sub (.var 4) (.const 1)) (.var 4)) (.ite (.and (.lt (.var 3) (.var 0)) (.lt (.var 4) (.const 3))) (.add (.var 4) (.const 1)) (.var 4)))],
  [],
  .le (.const 0) (.const 0),
  .or (.eq (.var 2) (.const 0)) (.eq (.var 2) (.const 1))⟩,
  []⟩
def pflight_proof : List MEntry := [⟨⟨.le (.var 3) (.add (.var 0) (.const 150)), none⟩, 5, [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .leaf [⟨[1], 151⟩, ⟨[(-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .split ⟨[0, 0, 1], 0⟩
  (.leaf [⟨[(-1), 0, 0, 1], (-150)⟩, ⟨[1, 0, 0, (-1)], 151⟩] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.split ⟨[0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, (-1)], 1⟩
  (.split ⟨[0, 1], (-50)⟩
  (.leaf [⟨[0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 1], (-50)⟩, ⟨[(-1), 0, 0, 1, 50], (-150)⟩, ⟨[1, (-1), 0, (-1)], 151⟩] [.input 0, .input 1, .input 2, .input 3, .combine 2 0 1 50, .combine 1 3 1 1, .combine 4 5 1 1] [] [])
  (.leaf [⟨[0, 0, 0, 0, (-1)], 1⟩, ⟨[(-1), 0, 0, 1, 50], (-150)⟩, ⟨[1, 0, 0, (-1)], 101⟩] [.input 0, .input 1, .input 2, .combine 1 0 1 50, .combine 3 2 1 1] [] []))
  (.leaf [⟨[(-1), 0, 0, 1], (-150)⟩, ⟨[1, 0, 0, (-1)], 151⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[], 1⟩] [.input 0] [] [])))⟩, ⟨⟨.le (.add (.var 3) (.mul 50 (.var 4))) (.add (.var 0) (.const 150)), none⟩, 5, [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .leaf [⟨[1], 151⟩, ⟨[(-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .split ⟨[0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 1], 1⟩
  (.split ⟨[0, 0, 0, 0, 1], (-2)⟩
  (.leaf [⟨[(-1), 0, 0, 1], 1⟩, ⟨[0, 0, 0, 0, 1], (-2)⟩, ⟨[1, 0, 0, (-1), (-50)], 101⟩] [.input 0, .input 1, .input 2, .combine 2 0 1 1, .cut 3 50 [0, 0, 0, 0, (-1)] 3, .combine 1 4 1 1] [] [])
  (.leaf [⟨[(-1), 0, 0, 1, 50], (-150)⟩, ⟨[1, 0, 0, (-1), (-50)], 151⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[(-1), 0, 0, 1, 50], (-150)⟩, ⟨[1, 0, 0, (-1), (-50)], 151⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, (-1)], 1⟩
  (.split ⟨[0, 1], (-50)⟩
  (.leaf [⟨[0, 1], (-50)⟩, ⟨[(-1), 0, 0, 1, 50], (-150)⟩, ⟨[1, (-1), 0, (-1), (-50)], 201⟩] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 3 1 1 1] [] [])
  (.leaf [⟨[(-1), 0, 0, 1, 50], (-150)⟩, ⟨[1, 0, 0, (-1), (-50)], 151⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[0, 0, 0, 0, 1], 0⟩, ⟨[(-1), 0, 0, 1], (-150)⟩, ⟨[1, 0, 0, (-1), (-50)], 151⟩] [.input 0, .input 1, .input 2, .combine 2 0 1 50, .combine 3 1 1 1] [] []))
  (.leaf [⟨[], 1⟩] [.input 0] [] [])))⟩]
theorem pflight_check : checkFMMachine pflight_machine pflight_proof = true := by decide +kernel
theorem pflight_laws : ∀ ρ M, FMReach pflight_machine ρ M → ∀ e ∈ pflight_proof, e.law.Holds ρ M :=
  fmmachine_sound pflight_machine pflight_proof pflight_check

-- Progress: in-flight: a request in flight can always complete
def flight_complete : Progress := ⟨.le (.const 1) (.var 4),
  .lt (.var 7) (.var 4),
  [(1, .const 0), (2, .const 1)],
  [(3, 6), (4, 7)],
  [],
  [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .leaf [⟨[], 1⟩] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .split ⟨[0, 0, 0, 0, (-1)], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [] [])
  (.leaf [⟨[0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))⟩
theorem flight_complete_holds : ProgressHolds pflight_machine flight_complete :=
  progress_sound pflight_machine pflight_proof flight_complete pflight_check (by decide +kernel)
-- TAMPERED: with none in flight, one completes (false): the proof above offered for it. Lean computes the check to false.
def flight_complete_tampered : Progress := ⟨.eq (.var 4) (.const 0),
  .lt (.var 7) (.var 4),
  [(1, .const 0), (2, .const 1)],
  [(3, 6), (4, 7)],
  [],
  [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .leaf [⟨[], 1⟩] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .split ⟨[0, 0, 0, 0, (-1)], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [] [])
  (.leaf [⟨[0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))⟩
example : checkProgress pflight_machine pflight_proof flight_complete_tampered = false := by decide +kernel

-- Progress: in-flight: under budget with room, one is admitted
def flight_admit : Progress := ⟨.and (.lt (.var 3) (.var 0)) (.lt (.var 4) (.const 3)),
  .eq (.var 7) (.add (.var 4) (.const 1)),
  [(1, .const 0), (2, .const 0)],
  [(3, 6), (4, 7)],
  [],
  [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .leaf [⟨[], 1⟩] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .split ⟨[(-1), 0, 0, 1], 1⟩
  (.split ⟨[0, 0, 0, 0, 1], (-2)⟩
  (.leaf [⟨[], 1⟩] [.input 0] [] [])
  (.leaf [⟨[0, 0, 0, 0, (-1)], 3⟩, ⟨[0, 0, 0, 0, 1], (-2)⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[1, 0, 0, (-1)], 0⟩, ⟨[(-1), 0, 0, 1], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))⟩
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
def padmit_proof : List MEntry := [⟨⟨.le (.get 0 (.var 8)) (.const 1), some 8⟩, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14], .leaf [⟨[], 1⟩] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .cell 0 ⟨[0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, (-1), 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 1, 0, 0, 0, 0, 0, (-1)], 0⟩
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 4 5 1 1] [(15, 19), (20, 24), (25, 29), (30, 34)] [])
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 0, (-1), 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 1, 0, 0, 0, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(15, 19), (20, 24), (25, 29), (30, 34)] [])
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 1 0 1 1] [(15, 19), (20, 24), (25, 29), (30, 34)] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 1 0 1 1] [(15, 19), (20, 24), (25, 29), (30, 34)] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 1 0 1 1] [(15, 19), (20, 24), (25, 29), (30, 34)] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 1 0 1 1] [(15, 19), (20, 24), (25, 29), (30, 34)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [(15, 19), (20, 24), (25, 29), (30, 34)] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩, ⟨⟨.le (.get 1 (.var 8)) (.var 0), some 8⟩, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14], .leaf [⟨[1], 1⟩, ⟨[(-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .cell 0 ⟨[0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, (-1), 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, (-1)], 0⟩
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(16, 19), (21, 24), (26, 29), (31, 34)] [])
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 0, 0, (-1), 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(16, 19), (21, 24), (26, 29), (31, 34)] [])
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(16, 19), (21, 24), (26, 29), (31, 34)] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(16, 19), (21, 24), (26, 29), (31, 34)] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [(16, 19), (21, 24), (26, 29), (31, 34)] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(16, 19), (21, 24), (26, 29), (31, 34)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [(16, 19), (21, 24), (26, 29), (31, 34)] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩, ⟨⟨.le (.get 2 (.var 8)) (.var 1), some 8⟩, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14], .leaf [⟨[0, 1], 1⟩, ⟨[0, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .cell 0 ⟨[0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, (-1), 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 1, 0, 0, 0, (-1)], 0⟩
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(17, 19), (22, 24), (27, 29), (32, 34)] [])
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 0, 0, 0, (-1), 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 1, 0, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(17, 19), (22, 24), (27, 29), (32, 34)] [])
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(17, 19), (22, 24), (27, 29), (32, 34)] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [(17, 19), (22, 24), (27, 29), (32, 34)] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(17, 19), (22, 24), (27, 29), (32, 34)] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(17, 19), (22, 24), (27, 29), (32, 34)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [(17, 19), (22, 24), (27, 29), (32, 34)] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩, ⟨⟨.le (.get 3 (.var 8)) (.var 2), some 8⟩, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14], .leaf [⟨[0, 0, 1], 1⟩, ⟨[0, 0, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .cell 0 ⟨[0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(18, 19), (23, 24), (28, 29), (33, 34)] [])
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(18, 19), (23, 24), (28, 29), (33, 34)] [])
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [(18, 19), (23, 24), (28, 29), (33, 34)] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(18, 19), (23, 24), (28, 29), (33, 34)] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(18, 19), (23, 24), (28, 29), (33, 34)] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(18, 19), (23, 24), (28, 29), (33, 34)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [(18, 19), (23, 24), (28, 29), (33, 34)] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩]
theorem padmit_check : checkFMMachine padmit_machine padmit_proof = true := by decide +kernel
theorem padmit_laws : ∀ ρ M, FMReach padmit_machine ρ M → ∀ e ∈ padmit_proof, e.law.Holds ρ M :=
  fmmachine_sound padmit_machine padmit_proof padmit_check

-- Progress: admit: an account under every cap gets its grant
def admit_grant : Progress := ⟨.and (.lt (.get 0 (.var 11)) (.const 1)) (.and (.lt (.get 1 (.var 12)) (.var 0)) (.and (.lt (.get 2 (.var 13)) (.var 1)) (.lt (.get 3 (.var 14)) (.var 2)))),
  .eq (.get 4 (.var 11)) (.const 1),
  [(3, .var 11), (4, .var 12), (5, .var 13), (6, .var 14), (7, .const 1)],
  [],
  [(0, 4), (1, 5), (2, 6), (3, 7)],
  [(0, .var 11), (0, .var 12), (0, .var 13), (0, .var 14), (1, .var 11), (1, .var 12), (1, .var 13), (1, .var 14), (2, .var 11), (2, .var 12), (2, .var 13), (2, .var 14), (3, .var 11), (3, .var 12), (3, .var 13), (3, .var 14)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .leaf [⟨[], 1⟩] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leaf [⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩, ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩, ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩, ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))⟩
theorem admit_grant_holds : ProgressHolds padmit_machine admit_grant :=
  progress_sound padmit_machine padmit_proof admit_grant padmit_check (by decide +kernel)
-- TAMPERED: even with the day full (false): the proof above offered for it. Lean computes the check to false.
def admit_grant_tampered : Progress := ⟨.and (.lt (.get 0 (.var 11)) (.const 1)) (.and (.lt (.get 2 (.var 13)) (.var 1)) (.lt (.get 3 (.var 14)) (.var 2))),
  .eq (.get 4 (.var 11)) (.const 1),
  [(3, .var 11), (4, .var 12), (5, .var 13), (6, .var 14), (7, .const 1)],
  [],
  [(0, 4), (1, 5), (2, 6), (3, 7)],
  [(0, .var 11), (0, .var 12), (0, .var 13), (0, .var 14), (1, .var 11), (1, .var 12), (1, .var 13), (1, .var 14), (2, .var 11), (2, .var 12), (2, .var 13), (2, .var 14), (3, .var 11), (3, .var 12), (3, .var 13), (3, .var 14)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .leaf [⟨[], 1⟩] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leaf [⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩, ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩, ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩, ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))⟩
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
def pfadmit_proof : List MEntry := [⟨⟨.le (.get 0 (.var 8)) (.const 1), some 8⟩, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15], .leaf [⟨[], 1⟩] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15, .cell 0 ⟨[0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, (-1), 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 1, 0, 0, 0, 0, 0, (-1)], 0⟩
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 4 5 1 1] [(16, 20), (21, 25), (26, 30), (31, 35)] [])
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 0, (-1), 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 1, 0, 0, 0, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(16, 20), (21, 25), (26, 30), (31, 35)] [])
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 1 0 1 1] [(16, 20), (21, 25), (26, 30), (31, 35)] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 1 0 1 1] [(16, 20), (21, 25), (26, 30), (31, 35)] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 1 0 1 1] [(16, 20), (21, 25), (26, 30), (31, 35)] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 1 0 1 1] [(16, 20), (21, 25), (26, 30), (31, 35)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [(16, 20), (21, 25), (26, 30), (31, 35)] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 2⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩, ⟨⟨.le (.get 1 (.var 8)) (.var 0), some 8⟩, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15], .leaf [⟨[1], 1⟩, ⟨[(-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15, .cell 0 ⟨[0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, (-1), 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, (-1)], 0⟩
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(17, 20), (22, 25), (27, 30), (32, 35)] [])
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 0, 0, (-1), 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(17, 20), (22, 25), (27, 30), (32, 35)] [])
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(17, 20), (22, 25), (27, 30), (32, 35)] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(17, 20), (22, 25), (27, 30), (32, 35)] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [(17, 20), (22, 25), (27, 30), (32, 35)] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(17, 20), (22, 25), (27, 30), (32, 35)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [(17, 20), (22, 25), (27, 30), (32, 35)] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩, ⟨⟨.le (.get 2 (.var 8)) (.var 1), some 8⟩, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15], .leaf [⟨[0, 1], 1⟩, ⟨[0, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15, .cell 0 ⟨[0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, (-1), 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 1, 0, 0, 0, (-1)], 0⟩
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(18, 20), (23, 25), (28, 30), (33, 35)] [])
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 0, 0, 0, (-1), 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 1, 0, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(18, 20), (23, 25), (28, 30), (33, 35)] [])
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(18, 20), (23, 25), (28, 30), (33, 35)] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [(18, 20), (23, 25), (28, 30), (33, 35)] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(18, 20), (23, 25), (28, 30), (33, 35)] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(18, 20), (23, 25), (28, 30), (33, 35)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [(18, 20), (23, 25), (28, 30), (33, 35)] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩, ⟨⟨.le (.get 3 (.var 8)) (.var 2), some 8⟩, 9, [(0, .var 3), (0, .var 4), (0, .var 5), (0, .var 6), (0, .var 9), (1, .var 3), (1, .var 4), (1, .var 5), (1, .var 6), (1, .var 9), (2, .var 3), (2, .var 4), (2, .var 5), (2, .var 6), (2, .var 9), (3, .var 3), (3, .var 4), (3, .var 5), (3, .var 6), (3, .var 9)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15], .leaf [⟨[0, 0, 1], 1⟩, ⟨[0, 0, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15, .cell 0 ⟨[0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(19, 20), (24, 25), (29, 30), (34, 35)] [])
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[0, 0, 0, 0, 0, 0, (-1), 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(19, 20), (24, 25), (29, 30), (34, 35)] [])
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [(19, 20), (24, 25), (29, 30), (34, 35)] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(19, 20), (24, 25), (29, 30), (34, 35)] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(19, 20), (24, 25), (29, 30), (34, 35)] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 0 3 1 1, .combine 1 2 1 1, .combine 5 4 1 1] [(19, 20), (24, 25), (29, 30), (34, 35)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [(19, 20), (24, 25), (29, 30), (34, 35)] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))⟩]
theorem pfadmit_check : checkFMMachine pfadmit_machine pfadmit_proof = true := by decide +kernel
theorem pfadmit_laws : ∀ ρ M, FMReach pfadmit_machine ρ M → ∀ e ∈ pfadmit_proof, e.law.Holds ρ M :=
  fmmachine_sound pfadmit_machine pfadmit_proof pfadmit_check

-- Progress: admit, the grant as a flag: an account under every cap gets its grant
def fadmit_grant : Progress := ⟨.and (.lt (.get 0 (.var 12)) (.const 1)) (.and (.lt (.get 1 (.var 13)) (.var 0)) (.and (.lt (.get 2 (.var 14)) (.var 1)) (.lt (.get 3 (.var 15)) (.var 2)))),
  .eq (.get 4 (.var 12)) (.const 1),
  [(3, .var 12), (4, .var 13), (5, .var 14), (6, .var 15), (7, .const 1)],
  [],
  [(0, 4), (1, 5), (2, 6), (3, 7)],
  [(0, .var 12), (0, .var 13), (0, .var 14), (0, .var 15), (1, .var 12), (1, .var 13), (1, .var 14), (1, .var 15), (2, .var 12), (2, .var 13), (2, .var 14), (2, .var 15), (3, .var 12), (3, .var 13), (3, .var 14), (3, .var 15)],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .leaf [⟨[], 1⟩] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .var 14, .var 15, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 1 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 2 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 3 ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.split ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])
  (.leaf [⟨[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩, ⟨[0, 0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩, ⟨[0, (-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩, ⟨[(-1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))⟩
theorem fadmit_grant_holds : ProgressHolds pfadmit_machine fadmit_grant :=
  progress_sound pfadmit_machine pfadmit_proof fadmit_grant pfadmit_check (by decide +kernel)

-- isolation: a.Acct[B] = b.Acct[B]  (variables 0 d, 1 hr, 2 dm, 3 Bacct, 4 Bday, 5 Bhour, 6 Bdom, 7 acct, 8 day, 9 hour, 10 dom, 11 ok, 12 who, 13 #; maps 0 a_Acct, 1 a_Day, 2 a_Hour, 3 a_Dom, 4 b_Acct, 5 b_Day, 6 b_Hour, 7 b_Dom)
def peracct_machine : FMMachine := ⟨⟨[7, 8, 9, 10, 11, 12],
  [],
  [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0)],
  [],
  [(0, .var 7, .ite (.and (.eq (.var 11) (.const 1)) (.lt (.get 0 (.var 7)) (.const 1))) (.add (.get 0 (.var 7)) (.const 1)) (.get 0 (.var 7))), (4, .var 7, .ite (.and (.eq (.ite (.eq (.var 12) (.const 1)) (.const 0) (.var 11)) (.const 1)) (.lt (.get 4 (.var 7)) (.const 1))) (.add (.get 4 (.var 7)) (.const 1)) (.get 4 (.var 7)))],
  .le (.const 0) (.const 0),
  .and (.or (.eq (.var 11) (.const 0)) (.eq (.var 11) (.const 1))) (.and (.or (.eq (.var 11) (.const 0)) (.eq (.var 11) (.const 1))) (.and (.or (.eq (.var 12) (.const 0)) (.eq (.var 12) (.const 1))) (.or (.and (.eq (.var 12) (.const 0)) (.and (.eq (.var 7) (.var 3)) (.and (.eq (.var 8) (.var 4)) (.and (.eq (.var 9) (.var 5)) (.eq (.var 10) (.var 6)))))) (.and (.eq (.var 12) (.const 1)) (.not (.eq (.var 7) (.var 3)))))))⟩,
  []⟩
def peracct_proof : List MEntry := [⟨⟨.eq (.get 0 (.var 3)) (.get 4 (.var 3)), none⟩, 13, [],
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13], .leaf [⟨[], 1⟩] [.input 0] [] []),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .var 8, .var 9, .var 10, .var 11, .var 12, .var 13, .cell 0 ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 4 ⟨[0, 0, 0, 0, 0, 0, 0, 1], 0⟩, .cell 0 ⟨[0, 0, 0, 1], 0⟩, .cell 4 ⟨[0, 0, 0, 1], 0⟩], .split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 1, 0, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, (-1), 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 2 0 1 1, .combine 1 4 1 1, .combine 5 3 1 1] [(14, 16), (15, 17)] [])
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 2 1 1 1, .combine 0 4 1 1, .combine 5 3 1 1] [(14, 16), (15, 17)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [] []))
  (.leaf [⟨[], 1⟩] [.input 0] [] []))
  (.split ⟨[0, 0, 0, (-1), 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 1, 0, 0, 0, (-1)], 0⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(14, 16), (15, 17)] [])
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))))
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 1, 0, 0, 0, (-1)], 0⟩
  (.split ⟨[0, 0, 0, (-1), 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], (-1)⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩] [.input 0, .input 1, .input 2, .combine 1 2 1 1, .combine 3 0 1 1] [(14, 16), (15, 17)] [])
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 0⟩] [.input 0, .input 1, .input 2, .combine 1 0 1 1, .combine 3 2 1 1] [(14, 16), (15, 17)] []))
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩] [.input 0, .input 1, .input 2, .input 3, .input 4, .combine 3 0 1 1, .combine 5 2 1 1, .combine 4 6 1 1, .combine 1 7 1 1] [(14, 16), (15, 17)] []))
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .input 4, .combine 4 1 1 1, .combine 3 2 1 1, .combine 0 6 1 1, .combine 7 5 1 1] [(14, 16), (15, 17)] [])
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 2 0 1 1, .combine 1 4 1 1, .combine 5 3 1 1] [(14, 16), (15, 17)] [])
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 0, 1], 0⟩] [.input 0, .input 1, .input 2, .input 3, .combine 2 1 1 1, .combine 0 4 1 1, .combine 5 3 1 1] [(14, 16), (15, 17)] []))))
  (.leaf [⟨[], 1⟩] [.input 0] [(14, 16), (15, 17)] []))
  (.leaf [⟨[], 1⟩] [.input 0] [] []))
  (.leaf [⟨[], 1⟩] [.input 0] [] []))
  (.split ⟨[0, 0, 0, (-1), 0, 0, 0, 1], 0⟩
  (.split ⟨[0, 0, 0, 1, 0, 0, 0, (-1)], 0⟩
  (.leaf [⟨[], 1⟩] [.input 0] [(14, 16), (15, 17)] [])
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))
  (.split ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 1⟩] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.leaf [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1), 1], 1⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, (-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])))))⟩]
theorem peracct_check : checkFMMachine peracct_machine peracct_proof = true := by decide +kernel
theorem peracct_laws : ∀ ρ M, FMReach peracct_machine ρ M → ∀ e ∈ peracct_proof, e.law.Holds ρ M :=
  fmmachine_sound peracct_machine peracct_proof peracct_check

-- spend roll-up, cap m a param: spend <= m count  (variables 0 m, 1 c, 2 spend, 3 count, 4 l_spend, 5 l_count, 6 r_spend, 7 r_count)
def rollupM_fold : Fold := ⟨[1],
  [(2, 4, 6), (3, 5, 7)],
  [(2, .min (.var 1) (.var 0)), (3, .const 1)],
  [(2, .add (.var 4) (.var 6)), (3, .add (.var 5) (.var 7))],
  .le (.const 0) (.const 0),
  .le (.const 0) (.const 0)⟩
def rollupM_proof : FoldProof := [(.le (.var 2) (.prod (.var 0) (.var 3)),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7], .split ⟨[(-1), 1], 0⟩
  (.leaf [⟨[], 1⟩] [.input 0] [] [])
  (.leaf [⟨[], 1⟩] [.input 0] [] [])),
  ([.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6, .var 7, .mono [0, 5], .mono [0, 7]], .leaf [⟨[0, 0, 0, 0, 1, 0, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, 0, 0, 1, 0, 0, (-1)], 0⟩, ⟨[0, 0, 0, 0, (-1), 0, (-1), 0, 1, 1], 1⟩] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 1 3 1 1] [] []))]
theorem rollupM_laws : ∀ maps ρ, evalC ρ maps rollupM_fold.pre = true → ∀ t, Allowed rollupM_fold ρ maps t →
    ∀ l ∈ rollupM_proof.map (·.1), evalC (foldT rollupM_fold ρ maps t) maps l = true :=
  fold_sound rollupM_fold rollupM_proof (by decide +kernel)

-- budget rule: bounded_loss: s <= b + m @start  (2 columns)
def t0_goal : Goal := ⟨[.var 0, .var 1],
  [.not (.le (.const 0) (.add (.var 0) (.var 1)))]⟩
def t0_tree : Tree :=
  .leaf [⟨[1, 1], 1⟩, ⟨[(-1)], 0⟩, ⟨[0, (-1)], 0⟩] [.input 0, .input 1, .input 2, .combine 0 1 1 1, .combine 3 2 1 1] [] []
theorem t0 : ∀ env maps, ¬ ∀ c ∈ t0_goal.hyps, evalC env maps c = true :=
  sound t0_goal t0_tree (by decide +kernel)

-- budget rule: bounded_loss: s <= b + m @step  (4 columns)
def t1_goal : Goal := ⟨[.var 0, .var 1, .var 2, .var 3],
  [.le (.var 0) (.add (.var 1) (.var 2)), .not (.le (.ite (.lt (.var 0) (.var 1)) (.add (.var 0) (.min (.var 3) (.var 2))) (.var 0)) (.add (.var 1) (.var 2)))]⟩
def t1_tree : Tree :=
  .split ⟨[1, (-1)], 1⟩
  (.split ⟨[0, 0, (-1), 1], 0⟩
  (.leaf [⟨[1, (-1)], 1⟩, ⟨[0, 0, (-1), 1], 0⟩, ⟨[(-1), 1, 1, (-1)], 1⟩] [.input 0, .input 1, .input 2, .combine 2 0 1 1, .combine 1 3 1 1] [] [])
  (.leaf [⟨[1, (-1)], 1⟩, ⟨[(-1), 1], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[1, (-1), (-1)], 0⟩, ⟨[(-1), 1, 1], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])
theorem t1 : ∀ env maps, ¬ ∀ c ∈ t1_goal.hyps, evalC env maps c = true :=
  sound t1_goal t1_tree (by decide +kernel)

-- in-flight: in-flight loss: s <= b + 3 × 50 @start  (1 columns)
def t2_goal : Goal := ⟨[.var 0],
  [.not (.le (.const 0) (.add (.var 0) (.const 150)))]⟩
def t2_tree : Tree :=
  .leaf [⟨[1], 151⟩, ⟨[(-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []
theorem t2 : ∀ env maps, ¬ ∀ c ∈ t2_goal.hyps, evalC env maps c = true :=
  sound t2_goal t2_tree (by decide +kernel)

-- in-flight: in-flight loss: s <= b + 3 × 50 @step  (5 columns)
def t3_goal : Goal := ⟨[.var 0, .var 1, .var 2, .var 3, .var 4],
  [.or (.eq (.var 0) (.const 0)) (.eq (.var 0) (.const 1)), .le (.var 1) (.add (.var 2) (.const 150)), .le (.add (.var 1) (.mul 50 (.var 3))) (.add (.var 2) (.const 150)), .not (.le (.ite (.and (.eq (.var 0) (.const 1)) (.lt (.const 0) (.var 3))) (.add (.var 1) (.min (.var 4) (.const 50))) (.var 1)) (.add (.var 2) (.const 150)))]⟩
def t3_tree : Tree :=
  .split ⟨[1], 0⟩
  (.leaf [⟨[0, 1, (-1)], (-150)⟩, ⟨[0, (-1), 1], 151⟩] [.input 0, .input 1, .combine 1 0 1 1] [] [])
  (.split ⟨[1], (-1)⟩
  (.split ⟨[0, 0, 0, (-1)], 1⟩
  (.split ⟨[0, 0, 0, 0, 1], (-50)⟩
  (.leaf [⟨[0, 0, 0, (-1)], 1⟩, ⟨[0, 0, 0, 0, 1], (-50)⟩, ⟨[0, 1, (-1), 50], (-150)⟩, ⟨[0, (-1), 1, 0, (-1)], 151⟩] [.input 0, .input 1, .input 2, .input 3, .combine 2 0 1 50, .combine 1 3 1 1, .combine 4 5 1 1] [] [])
  (.leaf [⟨[0, 0, 0, (-1)], 1⟩, ⟨[0, 1, (-1), 50], (-150)⟩, ⟨[0, (-1), 1], 101⟩] [.input 0, .input 1, .input 2, .combine 1 0 1 50, .combine 3 2 1 1] [] []))
  (.leaf [⟨[0, 1, (-1)], (-150)⟩, ⟨[0, (-1), 1], 151⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[], 1⟩] [.input 0] [] []))
theorem t3 : ∀ env maps, ¬ ∀ c ∈ t3_goal.hyps, evalC env maps c = true :=
  sound t3_goal t3_tree (by decide +kernel)

-- in-flight: s + 50p <= b + 150 @start  (1 columns)
def t4_goal : Goal := ⟨[.var 0],
  [.not (.le (.add (.const 0) (.mul 50 (.const 0))) (.add (.var 0) (.const 150)))]⟩
def t4_tree : Tree :=
  .leaf [⟨[1], 151⟩, ⟨[(-1)], 0⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []
theorem t4 : ∀ env maps, ¬ ∀ c ∈ t4_goal.hyps, evalC env maps c = true :=
  sound t4_goal t4_tree (by decide +kernel)

-- in-flight: s + 50p <= b + 150 @step  (5 columns)
def t5_goal : Goal := ⟨[.var 0, .var 1, .var 2, .var 3, .var 4],
  [.or (.eq (.var 0) (.const 0)) (.eq (.var 0) (.const 1)), .le (.var 1) (.add (.var 2) (.const 150)), .le (.add (.var 1) (.mul 50 (.var 3))) (.add (.var 2) (.const 150)), .not (.le (.add (.ite (.and (.eq (.var 0) (.const 1)) (.lt (.const 0) (.var 3))) (.add (.var 1) (.min (.var 4) (.const 50))) (.var 1)) (.mul 50 (.ite (.eq (.var 0) (.const 1)) (.ite (.lt (.const 0) (.var 3)) (.sub (.var 3) (.const 1)) (.var 3)) (.ite (.and (.lt (.var 1) (.var 2)) (.lt (.var 3) (.const 3))) (.add (.var 3) (.const 1)) (.var 3))))) (.add (.var 2) (.const 150)))]⟩
def t5_tree : Tree :=
  .split ⟨[1], 0⟩
  (.split ⟨[0, 1, (-1)], 1⟩
  (.split ⟨[0, 0, 0, 1], (-2)⟩
  (.leaf [⟨[0, 1, (-1)], 1⟩, ⟨[0, 0, 0, 1], (-2)⟩, ⟨[0, (-1), 1, (-50)], 101⟩] [.input 0, .input 1, .input 2, .combine 2 0 1 1, .cut 3 50 [0, 0, 0, (-1)] 3, .combine 1 4 1 1] [] [])
  (.leaf [⟨[0, 1, (-1), 50], (-150)⟩, ⟨[0, (-1), 1, (-50)], 151⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[0, 1, (-1), 50], (-150)⟩, ⟨[0, (-1), 1, (-50)], 151⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.split ⟨[1], (-1)⟩
  (.split ⟨[0, 0, 0, (-1)], 1⟩
  (.split ⟨[0, 0, 0, 0, 1], (-50)⟩
  (.leaf [⟨[0, 0, 0, 0, 1], (-50)⟩, ⟨[0, 1, (-1), 50], (-150)⟩, ⟨[0, (-1), 1, (-50), (-1)], 201⟩] [.input 0, .input 1, .input 2, .combine 0 2 1 1, .combine 3 1 1 1] [] [])
  (.leaf [⟨[0, 1, (-1), 50], (-150)⟩, ⟨[0, (-1), 1, (-50)], 151⟩] [.input 0, .input 1, .combine 1 0 1 1] [] []))
  (.leaf [⟨[0, 0, 0, 1], 0⟩, ⟨[0, 1, (-1)], (-150)⟩, ⟨[0, (-1), 1, (-50)], 151⟩] [.input 0, .input 1, .input 2, .combine 2 0 1 50, .combine 3 1 1 1] [] []))
  (.leaf [⟨[], 1⟩] [.input 0] [] []))
theorem t5 : ∀ env maps, ¬ ∀ c ∈ t5_goal.hyps, evalC env maps c = true :=
  sound t5_goal t5_tree (by decide +kernel)

-- products: x <= x·x  (4 columns)
def t6_goal : Goal := ⟨[.var 0, .mono [0, 0], .mono [0, 0, 0], .mono [0, 0, 0, 0]],
  [.not (.le (.var 0) (.prod (.var 0) (.var 0)))]⟩
def t6_tree : Tree :=
  .leaf [⟨[(-1), 1], 1⟩, ⟨[0, (-1)], 0⟩, ⟨[(-1)], 0⟩] [.input 0, .input 5, .input 7, .combine 1 0 1 1, .combine 3 2 1 1] [] [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)]
theorem t6 : ∀ env maps, ¬ ∀ c ∈ t6_goal.hyps, evalC env maps c = true :=
  sound t6_goal t6_tree (by decide +kernel)

-- TAMPERED: budget rule: bounded_loss: s <= b + m @step, the first leaf's derivation without its last step. Lean computes the check to false.
def tampered1_goal : Goal := ⟨[.var 0, .var 1, .var 2, .var 3],
  [.le (.var 0) (.add (.var 1) (.var 2)), .not (.le (.ite (.lt (.var 0) (.var 1)) (.add (.var 0) (.min (.var 3) (.var 2))) (.var 0)) (.add (.var 1) (.var 2)))]⟩
def tampered1_tree : Tree :=
  .split ⟨[1, (-1)], 1⟩
  (.split ⟨[0, 0, (-1), 1], 0⟩
  (.leaf [⟨[1, (-1)], 1⟩, ⟨[0, 0, (-1), 1], 0⟩, ⟨[(-1), 1, 1, (-1)], 1⟩] [.input 0, .input 1, .input 2, .combine 2 0 1 1] [] [])
  (.leaf [⟨[1, (-1)], 1⟩, ⟨[(-1), 1], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[1, (-1), (-1)], 0⟩, ⟨[(-1), 1, 1], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])
example : checkGoal tampered1_goal tampered1_tree = false := by decide +kernel

-- TAMPERED: the x <= x·x tree offered for x·x <= x. Lean computes the check to false.
def tampered1002_goal : Goal := ⟨[.var 0, .mono [0, 0], .mono [0, 0, 0], .mono [0, 0, 0, 0]],
  [.not (.le (.prod (.var 0) (.var 0)) (.var 0))]⟩
def tampered1002_tree : Tree :=
  .leaf [⟨[1, (-1)], 1⟩, ⟨[(-1)], 0⟩, ⟨[0, (-1)], 0⟩] [.input 0, .input 5, .input 7, .combine 1 0 1 1, .combine 3 2 1 1] [] [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)]
example : checkGoal tampered1002_goal tampered1002_tree = false := by decide +kernel

-- TAMPERED: budget rule: the bounded_loss tree offered for s <= b. Lean computes the check to false.
def tampered1001_goal : Goal := ⟨[.var 0, .var 1, .var 2, .var 3],
  [.le (.var 0) (.var 1), .not (.le (.ite (.lt (.var 0) (.var 1)) (.add (.var 0) (.min (.var 2) (.var 3))) (.var 0)) (.var 1))]⟩
def tampered1001_tree : Tree :=
  .split ⟨[1, (-1)], 1⟩
  (.split ⟨[0, 0, 1, (-1)], 0⟩
  (.leaf [⟨[1, (-1)], 1⟩, ⟨[0, 0, 1, (-1)], 0⟩, ⟨[(-1), 1, (-1)], 1⟩] [.input 0, .input 1, .input 2, .combine 2 0 1 1, .combine 1 3 1 1] [] [])
  (.leaf [⟨[1, (-1)], 1⟩, ⟨[(-1), 1, 0, (-1)], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] []))
  (.leaf [⟨[1, (-1)], 0⟩, ⟨[(-1), 1], 1⟩] [.input 0, .input 1, .combine 0 1 1 1] [] [])
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
