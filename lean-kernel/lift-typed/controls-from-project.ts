// Test-only data reduction from an already SOURCE_CHECKED project. No capsule
// load, restoration, search, emission or re-execution of public source proofs.
import {readFileSync,writeFileSync,mkdirSync,existsSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {join} from 'node:path'
const dir=process.argv[2]!,out=join(process.env.SUPERCOMPUTER_OUTPUT_DIR!,'controls')
const sha=(s:string|Uint8Array)=>createHash('sha256').update(s).digest('hex')
const receipt=JSON.parse(readFileSync(join(dir,'LIFT-CHECKED.json'),'utf8')),manifestBytes=readFileSync(join(dir,'EMITTED.json')),manifest=JSON.parse(manifestBytes.toString())
if(receipt.status!=='SOURCE_CHECKED'||sha(manifestBytes)!==receipt.emissionSha256||JSON.stringify(receipt.files)!==JSON.stringify(manifest.files))throw Error('controls require a hash-bound checked project')
mkdirSync(out)
for(const [name,hash]of Object.entries(manifest.files)) {
 const data=readFileSync(join(dir,name));if(createHash('sha256').update(data).digest('hex')!==hash)throw Error('checked source changed: '+name)
 const canonical=join('lean-kernel',name)
 if(name.endsWith('.lean')&&existsSync(canonical)&&sha(readFileSync(canonical))!==hash)throw Error('canonical root drift: '+name)
 writeFileSync(join(out,name),data)
}
const original=readFileSync(join(out,'BapaProof.lean'),'utf8'),marker=/\ntheorem [A-Za-z0-9_]+_options_complete :/.exec(original)
if(!marker)throw Error('checked typed data boundary absent')
const family=/^def (\w+)_retained_proof : List SEntry := \[([^\]]*)\]$/m.exec(original)
if(!family)throw Error('complete retained family list missing')
const id=family[1]!,members=family[2]!.split(',').map((s:string)=>s.trim()),decls=[...original.matchAll(new RegExp('^def '+id+'_retained_e(\\d+) : SEntry :=','gm'))]
if(!members.length||members.length!==decls.length||members.some((n:string,i:number)=>n!==id+'_retained_e'+i)||decls.some((m,i)=>Number(m[1])!==i))throw Error('incomplete retained entry family')
const derived=original.slice(0,marker.index)+'\n'
writeFileSync(join(out,'DataOnly.lean'),derived)
writeFileSync(join(out,'TypedControls.lean'),readFileSync(new URL('./TypedControls.lean',import.meta.url),'utf8'))
const control=readFileSync(join(dir,'FullRoleControl.lean'),'utf8')
if(!control.startsWith('import BapaProof\n'))throw Error('unexpected full-role control boundary')
writeFileSync(join(out,'FullRoleControl.lean'),control.replace('import BapaProof\n','import DataOnly\n')+`\ntheorem full_retained_family_present : ${id}_proof.length = ${members.length} := by decide +kernel\n#print axioms full_retained_family_present\n`)
writeFileSync(join(out,'ControlOrigin.json'),JSON.stringify({checkedReceiptSha256:sha(readFileSync(join(dir,'LIFT-CHECKED.json'))),checkedSourceSha256:manifest.files['BapaProof.lean'],derivedDataOnlySha256:sha(derived),cutMarker:marker[0],cutOffset:marker.index,expectedEntireEntryCount:members.length,retainedFamily:id+'_retained_proof',prefixUnchanged:derived===original.slice(0,marker.index)+'\n'},null,2))
