import Proofs
import RadixCertificateTransport
import BoundErasureReplay

namespace Bapa.ShardedKvTupleTransport
open Kern
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- These arities are the retained source's Table(node,key), Owner(key,node),
-- and TransferMsg(node,key,value), not inferred from arithmetic coefficients.
def layouts : List (Nat × Nat) := [(0,2),(1,2),(2,3)]
def outcome := RadixCertificateTransport.translate layouts 1000000 true
  captured_sharded_kv_0_machine captured_sharded_kv_0_proof

def succeeded : Bool := match outcome with | .ok _ => true | .error _ => false
-- Defaults below only make diagnostics total. A failed translation throws
-- before emission; no theorem or receipt may use these defaults as a lift.
def machine : SMachine := match outcome with
  | .ok p => p.1 | .error _ => captured_sharded_kv_0_machine
def proof : List SEntry := match outcome with
  | .ok p => p.2 | .error _ => captured_sharded_kv_0_proof

#eval (show IO Unit from do
  let out := (← IO.getEnv "SUPERCOMPUTER_OUTPUT_DIR").getD "."
  match outcome with
  | .error e =>
    IO.FS.writeFile (out ++ "/TRANSLATION-ERROR.txt") (reprStr e ++ "\n")
    throw (IO.userError ("tuple translation refused: " ++ reprStr e))
  | .ok (_,ps) =>
    IO.FS.writeFile (out ++ "/TRANSLATION-ACCEPTED.txt") "typed syntax phases completed; full kernel checking follows\n"
    let shift := match captured_sharded_kv_0_proof.head?, ps.head? with
      | some oldFirst, some newFirst => newFirst.step.1.length - oldFirst.step.1.length
      | _, _ => 0
    BoundErasureReplay.emitPlain out "ShardedKvTupleTransport"
      "Bapa.ShardedKvTupleTransport" machine ps (shift+1))
end Bapa.ShardedKvTupleTransport
