// Isolated negative controls, never source-acceptance receipts.
import {mkdirSync,writeFileSync,readFileSync} from 'node:fs'
import {join} from 'node:path'
import {x,n} from '../../core/machine.ts'
import {leanProject} from '../../lean-kernel/emit.ts'
import {answers,standard} from '../../scripts/lean-gate/gate.ts'
import {readFamilyCapsule} from './proof-codec.ts'
import {inspectProvenance,type NativeBundle} from './proof-capture.ts'
import {restoreTermPrelude} from './proof-prelude.ts'
import {alphaProposals,emitAlphaSource} from './source-projection.ts'
if(process.argv[2]==='--check-body'){
 const [dir,logPath]=process.argv.slice(3)
 if(!dir||!logPath)throw Error('control directory and log required')
 const meta=JSON.parse(readFileSync(join(dir,'NEGATIVE-CONTROL.json'),'utf8')),log=readFileSync(logPath,'utf8')
 const lines=[...log.matchAll(/error: BapaProof\.lean:(\d+):/g)].map(m=>Number(m[1]))
 if(meta.expected!=='body-equality-rejection'||lines.length!==1||lines[0]!==meta.failureLine)throw Error('failure was not the isolated body equality')
 const valid=answers(log).find(a=>a.name===meta.validTheorem)
 if(!valid||valid.axioms.some(a=>!standard.includes(a)))throw Error('body control did not independently check alpha validity')
 console.log('isolated body equality rejected; alpha validity checked')
 process.exit(0)
}
const [directory,sha,kind,out]=process.argv.slice(2)
if(!directory||!sha||!out||!['body','capture'].includes(kind??''))throw Error('expected CAPTURE SHA body|capture NEW_DIR')
const memos:[object,unknown][]=[]
const {data}=readFamilyCapsule(directory,sha,{maxBytes:134217728,maxNodes:1000000,maxStrings:100000,maxArrayLength:1000000,maxShards:1024},(o,m)=>memos.push([o,m]))
const bundle=data as NativeBundle
restoreTermPrelude(bundle.terms,memos)
if(bundle.route!=='inferred')throw Error('control requires inferred fixture')
const found=inspectProvenance(bundle.proof)
if(found.usual.length!==1||found.counted.length)throw Error('control requires unique usual producer')
const rename=alphaProposals(bundle.original.machine,found.usual[0]!.machine)[0]
if(!rename)throw Error('control needs a quantified binder rename')
const q=bundle.original.machine.step.flags![rename.flag]!
if(q.op!=='all')throw Error('missing quantified flag')
q.c=kind==='body'?{op:'not',x:q.c}:{op:'and',xs:[q.c,{op:'=',a:x(rename.fresh),b:n(0)}]}
const id='bapa_'+bundle.identity.protocol.replace(/[^A-Za-z0-9_]/g,'_'),full=emitAlphaSource(id,bundle)
const start=full.indexOf(`def ${id}_source :`),valid=full.indexOf(`theorem ${id}_alpha_valid :`),result=full.indexOf(`theorem ${id}_alpha_result :`)
if(start<0||valid<start||result<valid)throw Error('unexpected source emission layout')
const preamble='import QAlpha\nimport Ghost\nimport GhostMap\nopen Kern Cert\nset_option maxHeartbeats 200000000\nset_option maxRecDepth 100000\n'
let text:string,metadata:Record<string,unknown>
if(kind==='capture'){
 // No unrelated producer comparison: target is exactly the syntactically
 // renamed source. Shape equality holds, while the capture guard must be false.
 text=preamble+full.slice(start,valid)+`def ${id}_capture_target := QAlpha.renameAll ${id}_source ${id}_source_renames\ntheorem ${id}_capture_shape : QAlpha.renameAll ${id}_source ${id}_source_renames = ${id}_capture_target := by rfl\ntheorem ${id}_capture_rejected : QAlpha.validAll ${id}_source ${id}_source_renames = false := by decide +kernel\n#print axioms ${id}_capture_shape\n#print axioms ${id}_capture_rejected\n`
 metadata={role:'negative-control',expected:'capture-false-with-equal-shape',inputSha256:sha}
}else{
 const before=preamble+full.slice(0,result)+`#print axioms ${id}_alpha_valid\n`
 const failureLine=before.split('\n').length
 text=before+`theorem ${id}_body_bad : QAlpha.renameAll ${id}_source ${id}_source_renames = ${id}_machine := by rfl\n`
 metadata={role:'negative-control',expected:'body-equality-rejection',failureLine,validTheorem:id+'_alpha_valid',inputSha256:sha}
}
const project=leanProject(text,{name:'BapaProof'})
if(kind==='body')metadata.failureLine=project['BapaProof.lean']!.split('\n').findIndex(line=>line.startsWith(`theorem ${id}_body_bad :`))+1
mkdirSync(out)
for(const [name,content]of Object.entries(project))writeFileSync(join(out,name),content,{flag:'wx'})
writeFileSync(join(out,'NEGATIVE-CONTROL.json'),JSON.stringify(metadata,null,2)+'\n',{flag:'wx'})
