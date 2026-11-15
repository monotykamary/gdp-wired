// Custody receipt for an already completed retained-witness source build.
// This does not run Lean or establish correspondence independently of emission.
import {createHash} from 'node:crypto'
import {readFileSync,writeFileSync} from 'node:fs'
import {resolve,sep,join} from 'node:path'
import {answers,gate} from '../../scripts/lean-gate/gate.ts'
const sha=(text:string)=>createHash('sha256').update(text).digest('hex')
export function verifyWitnessSourceProject(directory:string,log:string) {
  const root=resolve(directory), raw=readFileSync(join(root,'EMITTED.json'),'utf8'), r=JSON.parse(raw)
  if(r.schema!=='bapa-emission/v1' || r.status!=='EMITTED_NOT_CHECKED' || r.route!=='witness' || r.sourceProjection?.kind!=='witness' || r.leanExecuted!==false || r.allSizesProven!==false) throw Error('not an unverified witness source emission')
  if(!/^[a-f0-9]{64}$/.test(r.inputSha256) || !r.files || typeof r.files!=='object') throw Error('invalid input/file manifest')
  for(const [name,digest] of Object.entries(r.files)) {
    const file=resolve(root,name)
    if(!file.startsWith(root+sep) || !/^[a-f0-9]{64}$/.test(String(digest)) || sha(readFileSync(file,'utf8'))!==digest) throw Error('emitted file changed: '+name)
  }
  if(!r.files['BapaProof.lean'] || !r.files['BoundGhost.lean']) throw Error('required witness source files missing')
  const id=r.identity?.protocol
  if(typeof id!=='string' || !/^[a-z][a-z0-9_]*$/.test(id)) throw Error('invalid protocol identity')
  const prefix='bapa_'+id, source:unknown[]=r.sourceProjection.sourceTheorems??[], names:unknown[]=r.sourceProjection.publicLawNames??[]
  if(r.familyTheorem!==prefix+'_laws' || !source.length || source.length!==names.length || names.some(x=>typeof x!=='string')) throw Error('public witness theorem coverage mismatch')
  if(source.some(x=>typeof x!=='string' || !new RegExp('^'+prefix+'_(?:ex|public)[0-9]+$').test(x))) throw Error('invalid source theorem names')
  const wanted=[r.familyTheorem,...source]
  if(new Set(wanted).size!==wanted.length) throw Error('duplicate source theorem names')
  const errors=gate(log,[readFileSync(join(root,'BapaProof.lean'),'utf8')],false)
  if(errors.length) throw Error(errors.join('; '))
  const found=new Set(answers(log).map(x=>x.name))
  for(const name of wanted) if(!found.has(name as string)) throw Error('missing exact theorem axiom output: '+name)
  if(!log.includes('Build completed successfully') || /\berror:/.test(log)) throw Error('no clean completed Lean build in log')
  return {schema:'bapa-source-check/v1',status:'SOURCE_CHECKED',inputSha256:r.inputSha256,emissionSha256:sha(raw),leanLogSha256:sha(log),identity:r.identity,sourceProjection:r.sourceProjection,checkedTheorems:wanted,files:r.files,leanVersion:r.leanVersion}
}
if(import.meta.main) {
  const [directory,logfile,out]=process.argv.slice(2)
  if(!directory || !logfile || !out) throw Error('usage: witness-source-verify.ts PROJECT LEAN_LOG NEW_RECEIPT')
  const result=verifyWitnessSourceProject(directory,readFileSync(logfile,'utf8'))
  writeFileSync(out,JSON.stringify(result,null,2)+'\n',{flag:'wx'})
  console.log(JSON.stringify(result))
}
