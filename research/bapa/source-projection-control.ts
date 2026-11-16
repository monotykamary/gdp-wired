// Explicit negative controls only. Never writes an acceptance receipt.
import {mkdirSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {x,n} from '../../core/machine.ts'
import {leanProject} from '../../lean-kernel/emit.ts'
import {readFamilyCapsule} from './proof-codec.ts'
import {inspectProvenance,type NativeBundle} from './proof-capture.ts'
import {restoreTermPrelude} from './proof-prelude.ts'
import {alphaProposals,emitAlphaSource} from './source-projection.ts'
const [directory,sha,kind,out]=process.argv.slice(2)
if(!directory||!sha||!out||!['body','capture'].includes(kind??''))throw Error('expected CAPTURE SHA body|capture NEW_DIR')
const memos:[object,unknown][]=[]
const {data}=readFamilyCapsule(directory,sha,{maxBytes:134217728,maxNodes:1000000,maxStrings:100000,maxArrayLength:1000000,maxShards:1024},(o,m)=>memos.push([o,m]))
const bundle=data as NativeBundle
restoreTermPrelude(bundle.terms,memos)
if(bundle.route!=='plain')throw Error('control requires plain fixture')
const found=inspectProvenance(bundle.proof)
if(found.usual.length!==1)throw Error('control requires unique producer')
const rename=alphaProposals(bundle.original.machine,found.usual[0]!.machine)[0]
if(!rename)throw Error('control needs an actual renamed quantified flag')
const q=bundle.original.machine.step.flags![rename.flag]!
if(q.op!=='all')throw Error('missing quantified flag')
q.c=kind==='body'?{op:'not',x:q.c}:{op:'and',xs:[q.c,{op:'=',a:x(rename.fresh),b:n(0)}]}
const id='bapa_'+bundle.identity.protocol.replace(/[^A-Za-z0-9_]/g,'_')
const body=emitAlphaSource(id,bundle)
const text='import QAlpha\nimport Ghost\nimport GhostMap\nopen Kern Cert\nset_option maxHeartbeats 200000000\nset_option maxRecDepth 100000\n'+body+'\n'
mkdirSync(out)
for(const [name,content]of Object.entries(leanProject(text,{name:'BapaProof'})))writeFileSync(join(out,name),content,{flag:'wx'})
writeFileSync(join(out,'NEGATIVE-CONTROL.json'),JSON.stringify({role:'negative-control',mutation:kind,expected:'lean-reject',inputSha256:sha})+'\n',{flag:'wx'})
