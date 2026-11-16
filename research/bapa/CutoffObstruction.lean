import Std

/- A negative control, not a cutoff theorem or a new checker rule.
   These are the connect branches of the fixed-radix lock-server encoding,
   with the domain guard enlarged separately from its unchanged radix. -/
namespace Bapa.CutoffObstruction

def pack (c s : Nat) : Nat := 64 * c + s
structure State where
  link : Nat → Nat
  semaphore : Nat → Nat

def initial : State := ⟨fun _ => 0, fun _ => 1⟩
def connect (st : State) (c s : Nat) : State :=
  if st.semaphore s = 1 then
    ⟨fun k => if k = pack c s then 1 else st.link k,
     fun k => if k = s then 0 else st.semaphore k⟩
  else st

def afterTwo : State := connect (connect initial 0 64) 0 0

theorem collision : pack 0 64 = pack 1 0 := by decide
theorem enlarged_domain : 0 < (2 : Nat) ∧ 1 < (2 : Nat) ∧ 64 < (65 : Nat) := by decide
theorem original_guard_refuses : ¬ 64 < (64 : Nat) := by decide
theorem requests_enabled : initial.semaphore 64 = 1 ∧
    (connect initial 0 64).semaphore 0 = 1 := by decide
theorem two_clients_at_server_zero :
    afterTwo.link (pack 0 0) = 1 ∧ afterTwo.link (pack 1 0) = 1 := by decide

theorem not_mutex : ¬ (∀ c₁ c₂ s : Nat, c₁ < 2 → c₂ < 2 → s < 65 →
    afterTwo.link (pack c₁ s) = 1 → afterTwo.link (pack c₂ s) = 1 → c₁ = c₂) := by
  intro h
  have bad := h 0 1 0 (by decide) (by decide) (by decide)
    two_clients_at_server_zero.1 two_clients_at_server_zero.2
  cases bad

#print axioms collision
#print axioms enlarged_domain
#print axioms original_guard_refuses
#print axioms requests_enabled
#print axioms two_clients_at_server_zero
#print axioms not_mutex
end Bapa.CutoffObstruction
