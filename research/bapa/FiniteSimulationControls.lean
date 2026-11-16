import FiniteSimulation

namespace Bapa.FiniteSimulationControls
open Bapa.FiniteSimulation

structure Scan where
  proposed : Bool
  busy : Bool
  cursor : Nat

-- A one-row negative control: Propose illegally omits the row condition;
-- the producer starts scanning but cannot commit a rejected row.
def atomicInitial (p : Bool) : Prop := p = false
def atomicPropose (p q : Bool) : Prop := p = false ∧ q = true
def scanInitial (s : Scan) : Prop := s = ⟨false,false,0⟩
inductive ScanStep : Scan → Scan → Prop where
  | start (p) : ScanStep ⟨p,false,0⟩ ⟨p,true,0⟩
  | rejected (p) : ScanStep ⟨p,true,0⟩ ⟨p,false,0⟩

def boundary (p : Bool) (s : Scan) : Prop := s.proposed = p ∧ s.busy = false

theorem bad_propose_reachable : Reachable atomicInitial atomicPropose true :=
  .next (.initial rfl) ⟨rfl,rfl⟩

theorem rejected_scan_never_proposes {s : Scan} (h : Reachable scanInitial ScanStep s) :
    s.proposed = false := by
  induction h with
  | initial hi => cases hi; rfl
  | next _ edge ih => cases edge <;> exact ih

/-- Even arbitrarily many finite stuttering steps cannot certify an atomic
Propose whose required scan row is false. This refutes the actual simulation
contract, not merely a syntactic shape check. -/
theorem unreproducible_propose_refused :
    ¬ ForwardSimulation atomicInitial atomicPropose scanInitial ScanStep boundary := by
  intro sim
  obtain ⟨s, hs, hp, _⟩ := sim.reaches bad_propose_reachable
  have hf := rejected_scan_never_proposes hs
  rw [hp] at hf
  cases hf

#print axioms bad_propose_reachable
#print axioms rejected_scan_never_proposes
#print axioms unreproducible_propose_refused
end Bapa.FiniteSimulationControls
