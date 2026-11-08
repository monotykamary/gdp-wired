// Static reduction only. No queries or changes to proof data.
import {existsSync,readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
const [directory]=process.argv.slice(2);if(!directory)throw new Error('OUTPUT_DIR required')
const read=(name:string)=>readFileSync(join(directory,name),'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l))
const demand=[...read('t2-t3.log'),...(existsSync(join(directory,'t2-hygiene.log'))?read('t2-hygiene.log'):[])],profile=existsSync(join(directory,'profile.log'))?[...read('control.log'),...read('profile.log')]:read('construction-leaves.log')
const t2=demand.filter(r=>r.measurement==='T2').map(r=>{
 const selection=r.selection,original=(i:number)=>selection.originalIndices[i],cuts=r.closureSteps.filter((e:any)=>e.stage==='closure-cut')
 const leaves=r.closureSteps.filter((e:any)=>e.stage==='closure-final').map((e:any)=>({...e,closedOriginalIndices:e.closedIndices.map(original)}))
 const attempts=r.closureSteps.filter((e:any)=>e.stage==='closure-source').map((e:any)=>({...e,originalIndex:original(e.index)}))
 return {law:r.law,targetScope:r.targetScope,witnessCleanup:selection.witnessCleanup===true,selection,conditionalTree:r.conditionalTree,conditionalChecked:r.conditionalChecked,wallMs:r.wallMs,complete:r.closureSteps.findLast((e:any)=>e.stage==='closure-complete'),cutCount:cuts.length,provedOriginalIndices:[...new Set(cuts.filter((c:any)=>c.index!==undefined).map((c:any)=>original(c.index)))],leaves,attempts}
})
const t3=demand.filter(r=>r.measurement==='T3').map(r=>({...r,numeric:undefined,result:undefined}))
const controls=profile.filter(r=>r.mode==='phase-census'&&!r.profiled),profiles=profile.filter(r=>r.mode==='phase-census'&&r.profiled)
const laws=profiles.map(r=>{
 const control=controls.find(c=>c.law===r.law),buckets=r.t1.buckets.other??{},construction=Object.fromEntries(Object.entries(buckets).filter(([k])=>k!=='admission'&&k!=='transport'))
 return {law:r.law,checked:r.checked,wallMs:r.wallMs,countedUnits:r.countedUnits,control:control&&{checked:control.checked,wallMs:control.wallMs,countedUnits:control.countedUnits},verdictMatches:control?.checked===r.checked,countedDelta:control?r.countedUnits-control.countedUnits:null,phases:r.phases,construction,constructionMs:Object.values(construction).reduce((sum:number,n)=>sum+Number(n),0),kernelChecks:r.t1.checks,detailSites:r.t1.sites}
})
const leafAudits=profile.filter(r=>r.test==='section7-followup-leaves')
for(const row of leafAudits)writeFileSync(join(directory,row.law.startsWith('Inv*')?'Invstar-leaves.json':row.law.split(':')[0].replaceAll(' ','-')+'-leaves.json'),JSON.stringify(row,null,2)+'\n')
const result={t2,t3,laws,leafAudits:leafAudits.map(r=>({...r,rows:undefined}))}
writeFileSync(join(directory,'results.json'),JSON.stringify(result,null,2)+'\n')
console.log(JSON.stringify(result))
