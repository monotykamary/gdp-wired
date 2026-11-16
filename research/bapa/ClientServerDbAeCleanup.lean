import ClientServerDbAeTransport
import CertificateBooleanCleanup

namespace Bapa.ClientServerDbAeCleanup
open Kern
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def machine := ClientServerDbAeTransport.machine
def proof := ClientServerDbAeTransport.proof.map
  (CertificateBooleanCleanup.entry machine ClientServerDbAeTransport.proof)

#eval (show IO Unit from do
  let out ← IO.getEnv "SUPERCOMPUTER_OUTPUT_DIR"
  BoundErasureReplay.emitPlain (out.getD ".") "ClientServerDbAeCleanup"
    "Bapa.ClientServerDbAeCleanup" machine proof)
end Bapa.ClientServerDbAeCleanup
