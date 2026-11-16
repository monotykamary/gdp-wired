import ClientServerDbAeSizedTransport
open Kern
namespace Bapa.ClientServerDbAeSizedTransport.Checked
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem obligations : Bapa.BoundErasureReplay.plainChecks Bapa.ClientServerDbAeSizedTransport.machine Bapa.ClientServerDbAeSizedTransport.proof = [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] := by decide +kernel
#print axioms obligations
theorem family : checkSMachine Bapa.ClientServerDbAeSizedTransport.machine Bapa.ClientServerDbAeSizedTransport.proof = true := by decide +kernel
#print axioms family
theorem laws : ∀ ρ M, SReach Bapa.ClientServerDbAeSizedTransport.machine ρ M → ∀ e ∈ Bapa.ClientServerDbAeSizedTransport.proof, e.Holds ρ M := smachine_sound _ _ family
#print axioms laws
def first : SEntry := Bapa.ClientServerDbAeSizedTransport.proof[0]'(by decide +kernel)
def bad : SEntry := Bapa.BoundErasureReplay.boundMutant first 3
theorem surviving_bound_refused : checkIn (sStepGoal Bapa.ClientServerDbAeSizedTransport.machine Bapa.ClientServerDbAeSizedTransport.proof bad) bad.step = false := by decide +kernel
#print axioms surviving_bound_refused
end Bapa.ClientServerDbAeSizedTransport.Checked
