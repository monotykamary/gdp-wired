// Consolidate already checked modules. This never calls Lean or a proof search.
import {createHash} from 'node:crypto'
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {answers,gate} from '../../scripts/lean-gate/gate.ts'
const sha=(x:string|Buffer)=>createHash('sha256').update(x).digest('hex')
const read=(p:string)=>readFileSync(p,'utf8')
const prefix='Bapa.SdlConcrete.'
const exact='Bapa.SimpleDecentralizedLockTransport.'
export function verifySdlSource(directory:string,dependencies:string){
 const records=JSON.parse(read(join(directory,'LEAN-RECEIPTS.json'))) as {module:string,sourceSHA256:string,exitCode:number,reused?:boolean,oleanSHA256?:string}[]
 const source=JSON.parse(read(join(directory,'SOURCE-DATA.json')))
 if(source.protocol!=='simple_decentralized_lock'||source.brokenSource===true||source.newProofSearches!==0)throw Error('not the unchanged SDL source')
 if(source.modelSHA256!==sha(readFileSync('research/protocols/ic3syn/models.ts'))||source.leanSHA256!==sha(read(join(directory,'SdlSourceDefs.lean')))||source.sourceSHA256!==sha(JSON.stringify({machine:source.machine,laws:source.laws})))throw Error('source data changed')
 const files:Record<string,string>={},modules:Record<string,unknown>={},found=new Set<string>()
 for(const r of records){
  if(!/^[A-Za-z][A-Za-z0-9]*$/.test(r.module)||r.exitCode!==0||modules[r.module])throw Error('invalid successful module receipt')
  const name=r.module+'.lean',text=read(join(directory,name))
  if(sha(text)!==r.sourceSHA256)throw Error('changed module '+r.module)
  const logfile=join(r.reused?dependencies:directory,r.module+'.log'),log=read(logfile)
  const errors=gate(log,[text],false)
  if(errors.length||/\.lean:\d+:\d+: error(?:\(|:)/.test(log))throw Error('module gate refused '+r.module+': '+errors.join(';'))
  for(const a of answers(log))found.add(a.name)
  const olean=sha(readFileSync(join(directory,'rechecked',r.module+'.olean')))
  if(r.oleanSHA256&&olean!==r.oleanSHA256)throw Error('changed compiled artifact '+r.module)
  files[name]=sha(text);modules[r.module]={sourceSHA256:r.sourceSHA256,oleanSHA256:olean,logSHA256:sha(log),reused:!!r.reused}
 }
 const required=[prefix+'target_eq',prefix+'proof_eq',prefix+'covers_eq',prefix+'Checked.obligations',prefix+'Checked.family',prefix+'Checked.laws',prefix+'Checked.surviving_bound_refused',prefix+'Checked.cover',prefix+'Checked.deleted',prefix+'Checked.missing_certificate',exact+'exact_sums',exact+'own_admission',exact+'public_base',exact+'mutual_exclusion',exact+'message_bound','sdl_reach','bapa_simple_decentralized_lock_source_law']
 for(const name of required)if(!found.has(name))throw Error('missing required theorem '+name)
 const rows=read(join(directory,'checks.tsv')).split('\n').map(x=>x.split('\t')).filter(x=>x[1]==='init'||x[1]==='step')
 if(rows.length!==8||rows.some(x=>x[2]!=='true')||!read(join(directory,'checks.tsv')).includes('family\tall\ttrue'))throw Error('incomplete SDL family')
 if(read(join(directory,'SDL-SUM-CHECK.txt'))!=='cover=true\ndeleted=false\nmissing=false\n')throw Error('incomplete exact SUM controls')
 const input='e123183e89e3d5e0378d9aaf3e4d00a5f7e55b3584821faf0c6fa2d739e82958'
 if(files['Proofs.lean']!=='95b20356ad9606abd1e4ea2489f8473c72b50451424b3ebdd2f13443528d5e2c')throw Error('wrong retained SDL proof')
 return {schema:'bapa-sdl-source-check/v1',status:'SOURCE_CHECKED',protocol:source.protocol,inputSha256:input,sourceSHA256:source.sourceSHA256,modelSHA256:source.modelSHA256,checkedTheorems:required,sourceTheorem:'bapa_simple_decentralized_lock_source_law',plainObligations:8,sumDeclarations:2,coverObligations:1,newProofSearches:0,allSizes:true,files,modules}
}
if(import.meta.main){
 const [directory,dependencies,out]=process.argv.slice(2)
 if(!directory||!dependencies||!out)throw Error('usage: sdl-source-verify.ts SOURCE_CHECKED_DIR DEPENDENCY_DIR NEW_RECEIPT')
 const result=verifySdlSource(directory,dependencies)
 writeFileSync(out,JSON.stringify(result,null,2)+'\n',{flag:'wx'})
 console.log(JSON.stringify(result))
}
