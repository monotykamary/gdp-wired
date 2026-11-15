// Fresh-process data-only export. No public proveRule/toLean/grow/search call.
import {createHash} from 'node:crypto'
import {mkdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {readFamilyCapsule, type ReadLimits} from './proof-codec.ts'
import {inspectProvenance, type NativeBundle} from './proof-capture.ts'
import {restoreTermPrelude} from './proof-prelude.ts'
import {emitAlphaSource} from './source-projection.ts'
import {retainedCMachineToLean, retainedSMachineToLean, leanProject} from '../../lean-kernel/emit.ts'

const hash=(s:string)=>createHash('sha256').update(s).digest('hex')
export function emitRetained(directory:string,sha256:string,out:string,limits:ReadLimits,options:{projection?:'none'|'alpha'}={}):Record<string,unknown> {
  const mode=options.projection??'none'
  if(mode!=='none'&&mode!=='alpha')throw Error('unsupported source projection mode')
  const metadata:[object,unknown][]=[]
  const {manifest,data}=readFamilyCapsule(directory,sha256,limits,(o,v)=>metadata.push([o,v]))
  const bundle=data as NativeBundle
  restoreTermPrelude(bundle.terms,metadata)
  const id='bapa_'+bundle.identity.protocol.replace(/[^A-Za-z0-9_]/g,'_')
  let body:string
  if(mode==='alpha')body=emitAlphaSource(id,bundle)
  else if(bundle.route==='counted-family')body=retainedCMachineToLean(id,bundle.final.machine,bundle.final.laws,bundle.final.proof)
  else {
    const found=inspectProvenance(bundle.proof)
    if(found.route==='witness')throw Error('witness source projection requires separately qualified export; capsule preserved')
    if(found.counted.length||found.usual.length!==1)throw Error('no unique retained usual family; capsule preserved')
    const leaf=found.usual[0]!
    body=retainedSMachineToLean(id,leaf.machine,leaf.laws,leaf.proof)
  }
  const sourceTheorems=mode==='alpha'?[id+'_source_laws',...bundle.original.laws.map((_,j)=>id+'_source_law'+j+'_holds')]:[]
  const printed=[id+'_laws',...sourceTheorems,...(mode==='alpha'?[id+'_alpha_valid',id+'_alpha_result']:[])]
  const text='import QAlpha\nimport Ghost\nimport GhostMap\nopen Kern Cert\nset_option maxHeartbeats 200000000\nset_option maxRecDepth 100000\n'+body+'\n'+printed.map(t=>'#print axioms '+t).join('\n')+'\n'
  if(/\b(?:sorry|axiom|native_decide)\b/.test(text))throw Error('unapproved Lean source construct')
  const project=leanProject(text,{name:'BapaProof'})
  const files=Object.fromEntries(Object.entries(project).map(([name,content])=>[name,hash(content)]))
  mkdirSync(out,{recursive:false})
  for(const [name,content]of Object.entries(project))writeFileSync(join(out,name),content,{flag:'wx'})
  const receipt={schema:'bapa-emission/v1',status:'EMITTED_NOT_CHECKED',inputSha256:sha256,identity:manifest.identity,
    route:bundle.route,projection:manifest.projection,familyTheorem:id+'_laws',files,
    ...(mode==='alpha'?{sourceProjection:{kind:'alpha',status:'EMITTED_NOT_CHECKED',sourceTheorems,publicLawNames:bundle.original.laws.map(l=>l.name)}}:{}),
    leanVersion:'4.34.0',leanExecuted:false,allSizesProven:false,
    publicSourceAcceptance:mode==='none'?'REQUIRES_SEPARATE_SOURCE_BRIDGE_AND_LEAN_CHECK':'REQUIRES_LEAN_SOURCE_PROJECTION_CHECK'}
  writeFileSync(join(out,'EMITTED.json'),JSON.stringify(receipt,null,2)+'\n',{flag:'wx'})
  return receipt
}
if(import.meta.main){
  const args=process.argv.slice(2),keys=new Set(['--capture','--sha256','--out','--max-bytes','--max-nodes','--projection']),v:Record<string,string>={}
  for(let i=0;i<args.length;i+=2){const k=args[i]!,value=args[i+1];if(!keys.has(k)||v[k]!==undefined||!value||value.startsWith('--'))throw Error('expected --capture DIR --sha256 HASH --out NEW_DIR [--max-bytes N] [--max-nodes N]');v[k]=value}
  if(!v['--capture']||!v['--sha256']||!v['--out'])throw Error('capture, SHA-256 and new output directory required')
  if(v['--projection']!==undefined&&!['none','alpha'].includes(v['--projection']))throw Error('projection must be none or alpha')
  const receipt=emitRetained(v['--capture'],v['--sha256'],v['--out'],{maxBytes:Number(v['--max-bytes']??134217728),maxNodes:Number(v['--max-nodes']??1000000),maxStrings:100000,maxArrayLength:1000000,maxShards:1024},{projection:v['--projection'] as 'none'|'alpha'|undefined})
  console.log(JSON.stringify(receipt))
}
