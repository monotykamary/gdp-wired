// Prepare exact historical trees and named diagnostic-only crossovers.
import {cpSync,readdirSync,readFileSync,writeFileSync,statSync} from 'node:fs'
import {join} from 'node:path'
import {execFileSync} from 'node:child_process'
import {createHash} from 'node:crypto'
const [work,root,out]=process.argv.slice(2);if(!work||!root||!out)throw new Error('WORK ROOT OUTPUT required')
const hash=(s:string|Buffer)=>createHash('sha256').update(s).digest('hex')
const files=(dir:string,prefix=''):string[]=>readdirSync(dir).sort().flatMap(n=>statSync(join(dir,n)).isDirectory()?files(join(dir,n),prefix+n+'/'):[prefix+n])
const manifest=(dir:string)=>Object.fromEntries(['core','kernel'].flatMap(p=>files(join(dir,p),p+'/')).map(p=>[p,hash(readFileSync(join(dir,p)))]))
const before={census:manifest(join(work,'census')),tf1:manifest(join(work,'tf1'))}
const productionDifferences=[...new Set([...Object.keys(before.census),...Object.keys(before.tf1)])].filter(p=>before.census[p]!==before.tf1[p])
if(productionDifferences.length)throw new Error('unexpected production-source difference: '+productionDifferences.join(','))
for(const p of ['package.json','bun.lock','tsconfig.json','.gitmodules'])if(hash(readFileSync(join(work,'census',p)))!==hash(readFileSync(join(work,'tf1',p))))throw new Error('dependency/config difference: '+p)
const variants=[{name:'census-profile',base:'census',profile:true,extra:false},{name:'tf1-profile',base:'tf1',profile:true,extra:true},{name:'tf1-minimal',base:'tf1',profile:true,extra:false},{name:'census-extras',base:'census',profile:true,extra:true},{name:'census-plain',base:'census',profile:false,extra:false},{name:'tf1-plain',base:'tf1',profile:false,extra:false}]
const records:any[]=[]
for(const v of variants){
 const dir=join(work,v.name);cpSync(join(work,v.base),dir,{recursive:true,dereference:false})
 const runner=join(dir,'research/track-m/run-phase-census.ts')
 let s=readFileSync(runner,'utf8');if(s.split('for(const prefix of prefixes){').length!==2)throw new Error('prefix anchor missing')
 // These are exactly the first three historical laws, in their original order.
 // No later law can affect them: auditing remains after the timed loop.
 s=s.replace('for(const prefix of prefixes){','for(const prefix of prefixes.slice(0,3)){');writeFileSync(runner,s)
 const install=(script:string,args:string[]=[])=>{const text=execFileSync(process.execPath,[script,...args],{cwd:dir,env:{...process.env,TRACK_M_DISPOSABLE_PROFILE:'1'},encoding:'utf8'});writeFileSync(join(out,v.name+'-'+script.split('/').at(-1)+'.log'),text)}
 if(v.extra){
  for(const file of ['install-section8-check-calls.ts','install-section8-progress.ts'])cpSync(join(root,'research/track-m',file),join(dir,'research/track-m',file))
  install('research/track-m/install-section8-check-calls.ts');install('research/track-m/install-section8-progress.ts')
 }
 if(v.profile)install('research/track-m/install-phase-census.ts',[join(work,v.name+'-originals')])
 const after=manifest(dir)
 records.push({...v,dir,production:after,meterHash:hash(readFileSync(join(dir,'research/track-m/phase-census-meter.ts'))),runnerHash:hash(readFileSync(runner))})
}
const postA=records.find(r=>r.name==='census-profile')!.production,postB=records.find(r=>r.name==='tf1-profile')!.production
const installedProductionDifferences=Object.keys(postA).filter(p=>postA[p]!==postB[p])
if(installedProductionDifferences.length)throw new Error('unequal installed production code')
writeFileSync(join(out,'source-manifest.json'),JSON.stringify({productionDifferences,installedProductionDifferences,before,variants:records,baselineCommits:{census:'38c17fc4',tf1:'bdb9568a'},kernelRulesChanged:false},null,2)+'\n')
console.log(JSON.stringify({prepared:variants.map(v=>v.name),productionDifferences,installedProductionDifferences}))
