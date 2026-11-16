import Proofs
import BoundErasureReplay

namespace Bapa.ClientServerDbAeTransport
open Kern
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def machine := CertificateBoundErasure.machine 64 captured_client_server_db_ae_0_machine
def proof := captured_client_server_db_ae_0_proof.map (CertificateBoundErasure.entry 64)

#eval (show IO Unit from do
  let out ← IO.getEnv "SUPERCOMPUTER_OUTPUT_DIR"
  Bapa.BoundErasureReplay.emitPlain (out.getD ".") "ClientServerDbAeTransport"
    "Bapa.ClientServerDbAeTransport" machine proof)
end Bapa.ClientServerDbAeTransport
