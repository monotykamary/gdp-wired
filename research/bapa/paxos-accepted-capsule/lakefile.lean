import Lake
open Lake DSL
package «paxos-accepted» where
lean_lib Paxos where
  roots := #[`PaxosEprAccepted]
