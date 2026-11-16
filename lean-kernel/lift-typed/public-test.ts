import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {liftMain} from '../../core/lift-cli.ts'
const out=process.env.SUPERCOMPUTER_OUTPUT_DIR!,project=join(out,'project')
const rc=await liftMain(['typed-client','research/bapa/lift-fixtures/client_server_db_ae.json','--sha256','e76ed2d24da036b98a98ea1edf509abe741499a2647c88f647c4d4f235cc87f0','--out',project,'--timeout-ms','1200000','--json'])
if(rc!==0)process.exit(rc)
const checked=JSON.parse(readFileSync(join(project,'LIFT-CHECKED.json'),'utf8')),emitted=JSON.parse(readFileSync(join(project,'EMITTED.json'),'utf8'))
if(checked.status!=='SOURCE_CHECKED'||emitted.sourceProjection.kind!=='typed-bound-substitution')throw Error('missing typed source acceptance')
writeFileSync(join(project,'TypedControls.lean'),readFileSync(new URL('./TypedControls.lean',import.meta.url),'utf8'))
// Independent domains: corrupt only machine annotation, retaining the complete
// original typed certificate family. The full checker, not a name comparison,
// must reject it.
writeFileSync(join(project,'FullRoleControl.lean'),`import BapaProof
open Kern Bapa.CertificateBoundSubstitution
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def wrongRoleTyping : Typed.Typing := {bapa_client_server_db_ae_baseTyping with variables := bapa_client_server_db_ae_baseTyping.variables.map fun (v,s) => (v, if s == bapa_client_server_db_ae_baseTyping.sizes[0]! then bapa_client_server_db_ae_baseTyping.sizes[1]! else s)}
def wrongRoleMachine : SMachine := (Typed.machine ${emitted.transport.bound} wrongRoleTyping bapa_client_server_db_ae_retained_machine).getD bapa_client_server_db_ae_retained_machine
theorem role_swap_complete_checker_refuses : checkSMachine wrongRoleMachine bapa_client_server_db_ae_proof = false := by decide +kernel
#print axioms role_swap_complete_checker_refuses
`)
console.log('PUBLIC_CLI_SOURCE_CHECKED',checked.checkedTheorems.length)
