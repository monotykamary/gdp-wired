import Proofs
import BoundErasureReplay
import CertificateBoundSubstitution

namespace Bapa.ClientServerDbAeSizedTransport
open Kern
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sizeVariable : Nat := 1000000
def machine := CertificateBoundSubstitution.machine 64 sizeVariable captured_client_server_db_ae_0_machine
def proof := captured_client_server_db_ae_0_proof.map (CertificateBoundSubstitution.entry 64 sizeVariable)

#eval (show IO Unit from do
  let out ← IO.getEnv "SUPERCOMPUTER_OUTPUT_DIR"
  BoundErasureReplay.emitPlain (out.getD ".") "ClientServerDbAeSizedTransport"
    "Bapa.ClientServerDbAeSizedTransport" machine proof 3)
end Bapa.ClientServerDbAeSizedTransport
