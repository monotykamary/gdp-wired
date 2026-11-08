// Section 8.1 prototype in a disposable snapshot, never a production patch.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw new Error('disposable Linux snapshot required')
const file='core/count-recovery/derivability-closure.ts';let s=readFileSync(file,'utf8')
const replace=(a:string,b:string)=>{if(s.split(a).length!==2)throw new Error('nonunique loop marker '+a);s=s.replace(a,b)}
replace(' const alive=()=>clock()<until&&!pastWall(),building=()=>clock()<buildEnd&&!pastWall()', ' let leafEnd:number|undefined\n const alive=()=>clock()<until&&!pastWall(),building=()=>clock()<(leafEnd??buildEnd)&&!pastWall()')
replace('Math.max(0,until-clock())*10', 'Math.max(0,(leafEnd??until)-clock())*10')
let start=s.indexOf(' const failed=new Map<string,number>();'),end=s.indexOf(' // Phase C only:',start)
if(start<0||end<0)throw new Error('missing sweep')
s=s.slice(0,start)+readFileSync('research/track-m/section8-loop-source.txt','utf8')+s.slice(end)
start=s.indexOf(' const finish=(scope:Path,end:number):Tree|undefined=>{');end=s.indexOf(' const scalar=',start)
if(start<0||end<0)throw new Error('missing finish')
s=s.slice(0,start)+readFileSync('research/track-m/section8-loop-finish.txt','utf8')+s.slice(end)
writeFileSync(file,s)
const f='core/count-recovery/field-bound-lemmas.ts',before=readFileSync(f,'utf8'),marker='  if(closed)return closed\n }\n // Split a packed field'
if(before.split(marker).length!==2)throw new Error('missing closure call')
writeFileSync(f,before.replace(marker,"  return closed // T-8.1 measures the loop, not the legacy fallback after failure\n }\n // Split a packed field"))
const probe='research/track-m/active-source-probe.ts';let p=readFileSync(probe,'utf8')
p=p.replace('clock,counted,fullRate,','clock,counted,fullRate,fullWork,').replace('captured=new Set<string>(),start=performance.now()','captured=new Set<string>(),workBefore=fullWork(),start=performance.now()').replace('wallMs:performance.now()-start,conditionalTree:','countedUnits:(fullWork()-workBefore)/fullRate,wallMs:performance.now()-start,conditionalTree:')
writeFileSync(probe,p)
console.log(JSON.stringify({installed:'T-8.1',researchOnly:true,sourceReuseBindingGuard:true,leafAllowance:350,sourceAllowance:[50,150]}))
