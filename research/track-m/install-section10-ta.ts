// Extend the captured observer packet only, never the preceding search.
import {readFileSync,writeFileSync} from 'node:fs'
import {execFileSync} from 'node:child_process'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw new Error('disposable Linux snapshot required')
execFileSync(process.execPath,['research/track-m/install-section9-ta.ts'],{stdio:'inherit'})
for(const [file,old,next]of [
 ['core/count-recovery/derivability-closure.ts','../../research/track-m/section9-guard-observer.ts','../../research/track-m/section10-inclusion-observer.ts'],
 ['research/track-m/active-source-probe.ts','./section9-guard-observer.ts','./section10-inclusion-observer.ts']]){
 let text=readFileSync(file!,'utf8');if(text.split(old!).length!==2)throw new Error('missing observer import');text=text.replace(old!,next!)
 if(file!.endsWith('active-source-probe.ts')){
  text=text.replace("import {s9 as __s9} from './section10-inclusion-observer.ts'","import {s9 as __s9,setSection10Builder} from './section10-inclusion-observer.ts'")
  const marker=' __s9.begin(law.name,selection,__s9Full)'
  if(text.split(marker).length!==2)throw new Error('missing observer setup anchor')
  const setup=` setSection10Builder(q=>{
  const cert={...packet.cert,insts:[...packet.cert.insts,q]},localAt=seedCountWitnessFlags(m,at,[{...packet,cert}],true)
  const raw=countedObligations(m,laws,{[law.name]:localAt},index).find(p=>p.goal.name.endsWith('@step'))
  if(!raw)throw new Error('fresh witness obligations missing')
  const g=mcGoal(raw.goal.hyps,raw.decls,cert)
  if(!g)throw new Error('fresh witness certificate rejected')
  return {g:{...g,hyps:[guard,...g.hyps]},cert}
 })
`
  text=text.replace(marker,setup+marker)
 }
 writeFileSync(file!,text)
}
console.log(JSON.stringify({installed:'T-10A',addedInstances:1,addition:'observer-only after exact capture',freshWitness:'s10$inclusion',productionChanged:false}))
