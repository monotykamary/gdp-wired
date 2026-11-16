// Rebuild the accepted SDL transport from current library sources and frozen input terms.
// No search. The existing SDL replay rechecks every dependency and source theorem.
import {createHash} from 'node:crypto'
import {readFileSync, writeFileSync, mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {spawnSync} from 'node:child_process'
import {leanProject} from '../../lean-kernel/emit.ts'
const root=process.cwd(), out=process.env.SUPERCOMPUTER_OUTPUT_DIR!
if(!out)throw Error('run through supercomputer')
const sha=(x:string|Uint8Array)=>createHash('sha256').update(x).digest('hex')
const source=join(root,'release-proofs/simple_decentralized_lock')
const raw=readFileSync(join(source,'Proofs.lean'),'utf8')
if(sha(raw)!=='95b20356ad9606abd1e4ea2489f8473c72b50451424b3ebdd2f13443528d5e2c')throw Error('wrong SDL proof')
const familyRaw=readFileSync(join(source,'FAMILY-CHECK.json'),'utf8'), family=JSON.parse(familyRaw)
if(family.capsuleSHA256!=='e123183e89e3d5e0378d9aaf3e4d00a5f7e55b3584821faf0c6fa2d739e82958')throw Error('wrong SDL capsule binding')
const retained=join(root,'sdl-retained'), project=join(retained,'lean')
mkdirSync(project,{recursive:true})
writeFileSync(join(retained,'FAMILY-CHECK.json'),familyRaw,{flag:'wx'})
for(const [name,text]of Object.entries(leanProject(raw,{name:'Proofs'})))writeFileSync(join(project,name),text,{flag:'wx'})
function run(args:string[],cwd:string,name:string){
 const p=spawnSync(args[0]!,args.slice(1),{cwd,env:process.env,encoding:'utf8',timeout:600000,maxBuffer:32*1024*1024})
 writeFileSync(join(out,name+'.log'),(p.stdout??'')+(p.stderr??''),{flag:'wx'})
 if(p.error||p.status!==0)throw Error(name+' failed: '+String(p.error??p.status))
}
try{
 run(['lake','build'],project,'fresh-library')
 run([process.execPath,join(root,'research/bapa/sdl-source-data.ts')],root,'source-data')
 run(['python3',join(root,'research/bapa/sdl-transport-replay.py')],root,'sdl-replay')
 const receipt=readFileSync(join(out,'SOURCE-CHECKED.json'),'utf8')
 if(JSON.parse(receipt).status!=='SOURCE_CHECKED')throw Error('SDL source receipt missing')
 writeFileSync(join(out,'RELEASE-REPLAY.json'),JSON.stringify({schema:'bapa-release-replay/v1',id:'simple_decentralized_lock',status:'SOURCE_CHECKED',noSearch:true,sourceRevision:process.env.BAPA_RELEASE_COMMIT,inputSha256:family.capsuleSHA256,proofSha256:sha(raw),familyReceiptSha256:sha(familyRaw),sourceCheckSha256:sha(receipt)},null,2)+'\n',{flag:'wx'})
}catch(error){
 writeFileSync(join(out,'RELEASE-REPLAY.json'),JSON.stringify({schema:'bapa-release-replay/v1',id:'simple_decentralized_lock',status:'FAILED',noSearch:true,sourceRevision:process.env.BAPA_RELEASE_COMMIT,reason:String(error)},null,2)+'\n',{flag:'wx'})
 throw error
}
