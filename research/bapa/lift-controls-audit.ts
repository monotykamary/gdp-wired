// Audit-only reuse of completed native controls. Never re-execute their proofs.
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {auditLiftLog} from '../../lean-kernel/axiom-audit.ts'
import {assert,hash,hashFile,json,verifyFiles} from './lift-regression.ts'
const [evidence,project]=process.argv.slice(2)
assert(process.argv.length===4&&evidence&&project,'usage: lift-controls-audit.ts CONTROL_DIRECTORY CHECKED_PROJECT')
const origin=json<any>(join(evidence,'controls/ControlOrigin.json'))
const checked=json<any>(join(project,'LIFT-CHECKED.json')),manifestPath=join(project,'EMITTED.json'),manifest=json<any>(manifestPath)
assert(checked.status==='SOURCE_CHECKED'&&checked.emissionSha256===hashFile(manifestPath),'public source receipt mismatch')
assert(hashFile(join(project,'LIFT-CHECKED.json'))===origin.checkedReceiptSha256,'control receipt origin changed')
verifyFiles(project,manifest.files)
assert(JSON.stringify(checked.files)===JSON.stringify(manifest.files),'public receipt file inventory mismatch')
const root=readFileSync(join(project,'BapaProof.lean'),'utf8'),data=readFileSync(join(evidence,'controls/DataOnly.lean'),'utf8')
assert(hash(root)===origin.checkedSourceSha256&&hash(data)===origin.derivedDataOnlySha256,'retained data hashes changed')
assert(origin.prefixUnchanged===true&&Number.isSafeInteger(origin.cutOffset)&&root.slice(origin.cutOffset).startsWith(origin.cutMarker),'invalid retained data boundary')
assert(data===root.slice(0,origin.cutOffset)+'\n','control data is not the exact original prefix')
const family=/^def (\w+)_retained_proof : List SEntry := \[([^\]]*)\]$/m.exec(data)
assert(family,'complete retained family declaration absent')
const id=family[1]!,members=family[2]!.split(',').map(n=>n.trim()),declarations=[...data.matchAll(new RegExp('^def '+id+'_retained_e(\\d+) : SEntry :=','gm'))]
assert(origin.retainedFamily===id+'_retained_proof'&&origin.expectedEntireEntryCount===27,'unexpected retained family contract')
assert(members.length===27&&declarations.length===27&&members.every((n,i)=>n===id+'_retained_e'+i)&&declarations.every((m,i)=>Number(m[1])===i),'incomplete retained family data')
const names=['TypedControls.independently_typed','TypedControls.swap_not_equivalent','TypedControls.wrong_sort_is_false','TypedControls.row_keeps_independent_parameter','role_swap_complete_checker_refuses','full_retained_family_present']
const logs=['typed-controls.log','full-role-control.log'],text=logs.map(n=>readFileSync(join(evidence,n),'utf8')).join('\n')
const theorems=auditLiftLog(text,[],names)
console.log(JSON.stringify({schema:'gdp-lift-controls-audit/v1',status:'CONTROLS_CHECKED',reexecuted:false,retainedEntries:27,origin,logs:Object.fromEntries(logs.map(n=>[n,hashFile(join(evidence,n))])),theorems},null,2))
