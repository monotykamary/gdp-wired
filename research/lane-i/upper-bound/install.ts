// Edits ONLY a disposable Linux research copy; hashes bind every change.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux copy required')
const mode=process.argv[2];if(mode!=='on'&&mode!=='off')throw Error('on|off required')
const hash=(s:string)=>createHash('sha256').update(s).digest('hex'),changes:{path:string,before:string,after:string,edits:string[]}[]=[]
function change(path:string,fn:(s:string,notes:string[])=>string){const before=readFileSync(path,'utf8'),notes:string[]=[],after=fn(before,notes);writeFileSync(path,after);changes.push({path,before:hash(before),after:hash(after),edits:notes})}
function replace(s:string,a:string,b:string,notes:string[],all=false){const n=s.split(a).length-1;if(!n||!all&&n!==1)throw Error(`anchor ${n}: ${a}`);notes.push(`${n}x ${a} => ${b}`);return all?s.split(a).join(b):s.replace(a,b)}
change('core/counts.ts',(s,n)=>{
 s=replace(s,"const obligations = (i: Instances) => ptime('encode', () => countedObligations(m, ls, {[law.name]: i}, ls.indexOf(law)))","const obligations = (i: Instances) => ptime('encode', () => countedObligations(m, ls, {[law.name]: i}, ls.indexOf(law)).filter(({goal}) => goal.name.endsWith('@step')))",n)
 const line=s.split('\n').find(l=>l.trim().startsWith('const contexts = '));if(!line)throw Error('contexts line missing')
 s=replace(s,line,"      const contexts: {local: Law[], fraction: number, kind: string}[] = [] // research: full captured family only, no shared context probe",n)
 if(mode==='off')s=replace(s,'Math.min(attemptEnd, clock() + Math.min(ms, 5000))','attemptEnd',n,true)
 return s
})
const paths=['core/count-cases.ts','core/count-focus-proof.ts','core/count-recovery/derivability-closure.ts','core/count-recovery/guard-cases.ts','core/count-recovery/field-bound-lemmas.ts','core/count-recovery/row-cases.ts']
for(const path of paths)change(path,(s,n)=>{
 const prefix=path.startsWith('core/count-recovery/')?"import {upperControl as __upper} from '../../research/lane-i/upper-bound/control.ts'\n":"import {upperControl as __upper} from '../research/lane-i/upper-bound/control.ts'\n"
 s=prefix+s
 if(s.includes('trace.push('))s=replace(s,'trace.push(','__upper.push(trace,',n,true)
 if(path==='core/count-focus-proof.ts')s=replace(s,"  if(clock()>=until||pastWall()||!m.inputMaps?.length)return undefined","  trace ??= e=>__upper.event(e)\n  if(clock()>=until||pastWall()||!m.inputMaps?.length)return undefined",n)
 if(path==='core/count-recovery/derivability-closure.ts'){
  s=replace(s,'  excludedAt.set(scopeKey,excluded);leafEnd=end','  excludedAt.set(scopeKey,excluded);leafEnd=end\n  __upper.event({stage:"upper-leaf-enter",path:[...scope],excluded:[...excluded],end})',n)
  s=replace(s,'      if(allSat&&!proved)excluded.add(index)','      if(allSat&&!proved){excluded.add(index);__upper.event({stage:"upper-excluded",path:[...scope],index,excluded:[...excluded]})}',n)
 }
 if(mode==='off'){
  // Remove local time/count sub-deadlines; keep logical search-width/depth heuristics.
  s=s.replace(/Math\.min\((until|end|caseEnd|limit|buildEnd),\s*clock\(\)\s*\+\s*\d+(?:_\d+)?\)/g,(_m,x:string)=>{n.push(_m+' => '+x);return x})
  if(path==='core/count-recovery/guard-cases.ts')s=replace(s,'end=active?Math.min(until,start+leafAllowance(until-start,1)):Math.min(until,start+500)','end=until',n)
  if(path==='core/count-recovery/derivability-closure.ts'){
   s=replace(s,'Math.min(wallAt(),performance.now()+Math.min(10000,Math.max(0,(leafEnd??until)-clock())*10))','wallAt()',n)
   s=replace(s,'Math.min(end,clock()+(inst.terms.length===5?150:50))','end',n)
   s=replace(s,'Math.min(end,independent?before+150:Math.max(queryLimit,clock()+100))','end',n)
  }
  if(path==='core/count-recovery/field-bound-lemmas.ts'){
   s=replace(s,'finish?Math.max(0,until-clock()):250','Math.max(0,until-clock())',n)
   s=replace(s,'const copyUntil=diagonalCopy(inst)?Math.max(clock(),until-200):Math.min(until,started+230)','const copyUntil=until',n)
   s=replace(s,'solve(part,directCopy?Math.max(0,230-(clock()-started)):150)','solve(part,Math.max(0,until-clock()))',n)
   s=replace(s,'Math.min(until,started+(directCopy?230:150))','until',n)
  }
  if(path==='core/count-focus-proof.ts')s=replace(s,'queryMs:200','queryMs:1e12',n)
 }
 return s
})
if(mode==='off')change('core/count-recovery/leaf-allowance.ts',(s,n)=>replace(s,'return Math.min(available/Math.max(1,leavesLeft),available/3)','return available',n))
writeFileSync('upper-patches.json',JSON.stringify({researchOnly:true,ceilings:mode,notes:'No share; original full family; STEP only. Off removes local deadline ceilings, not logical search-depth or candidate-width heuristics. Kernel files unchanged.',changes},null,2))
console.log('UPPER_PATCHES '+JSON.stringify({ceilings:mode,files:changes.map(x=>({path:x.path,before:x.before,after:x.after,edits:x.edits.length}))}))
