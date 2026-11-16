import ShardedKvTupleTransport
open Kern
namespace Bapa.ShardedKvTupleTransport.Checked
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem obligations : Bapa.BoundErasureReplay.plainChecks Bapa.ShardedKvTupleTransport.machine Bapa.ShardedKvTupleTransport.proof = [true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false] := by decide +kernel
#print axioms obligations
theorem family : checkSMachine Bapa.ShardedKvTupleTransport.machine Bapa.ShardedKvTupleTransport.proof = false := by decide +kernel
#print axioms family
def first : SEntry := Bapa.ShardedKvTupleTransport.proof[0]'(by decide +kernel)
def bad : SEntry := Bapa.BoundErasureReplay.boundMutant first 4
theorem surviving_bound_refused : checkIn (sStepGoal Bapa.ShardedKvTupleTransport.machine Bapa.ShardedKvTupleTransport.proof bad) bad.step = false := by decide +kernel
#print axioms surviving_bound_refused
end Bapa.ShardedKvTupleTransport.Checked
