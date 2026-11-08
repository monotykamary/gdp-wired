// Extract bounded report tables and independent proof-use replay inputs from JSONL.
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
const [log,out]=process.argv.slice(2)
if(!log||!out)throw new Error('LOG OUTPUT_DIR required')
mkdirSync(out,{recursive:true})
const records=readFileSync(log,'utf8').split('\n').filter(s=>s.startsWith('{')).flatMap(s=>{try{const r=JSON.parse(s);return r.mode==='phase-census'?[r]:[]}catch{return []}})
const summaries:any[]=[],comparisons:any[]=[],replay:any[]=[]
for(const r of records){
 const prefix=['one primary','Inv3915','Inv1758','Inv2973','Inv*'].find(p=>r.law.startsWith(p))!.replace('*','star').replaceAll(' ','-')
 const id=`${r.side}-${r.entry}-${r.profiled?'profiled':'control'}-${prefix}`
 const {proofAudit,...report}=r
 writeFileSync(join(out,id+'.json'),JSON.stringify(report)+'\n')
 if(proofAudit.length){writeFileSync(join(out,id+'-proofs.json'),JSON.stringify(proofAudit)+'\n');replay.push({id,file:id+'-proofs.json',leaves:proofAudit.length})}
 summaries.push({id,side:r.side,entry:r.entry,profiled:r.profiled,warmup:r.warmup,law:r.law,proven:r.proven,checked:r.checked,wallMs:r.wallMs,countedUnits:r.countedUnits,phases:r.phases,auditWallMs:r.auditWallMs,cutCounts:r.cutCounts,leafCount:r.leaves.length,checkedLeaves:r.leaves.filter((l:any)=>l.checked).length,phaseAccountingErrorMs:Math.abs(r.accountedMs-r.wallMs)})
}
for(const r of summaries.filter(r=>r.profiled)){
 const control=summaries.find(c=>!c.profiled&&c.side===r.side&&c.entry===r.entry&&c.law===r.law)
 if(!control)throw new Error('missing control '+r.id)
 comparisons.push({profiled:r.id,control:control.id,sameVerdict:r.proven===control.proven&&r.checked===control.checked,sameCountedWork:Math.abs(r.countedUnits-control.countedUnits)<1e-6,countedDifference:r.countedUnits-control.countedUnits,controlWallMs:control.wallMs,profiledWallMs:r.wallMs,wallRatio:r.wallMs/control.wallMs})
}
const verification={records:records.length,profiled:comparisons.length,allVerdictsMatch:comparisons.every(r=>r.sameVerdict),allCountedWorkMatches:comparisons.every(r=>r.sameCountedWork),accountingWithinOneMs:summaries.filter(r=>r.profiled).every(r=>r.phaseAccountingErrorMs<1),comparisons,replay}
writeFileSync(join(out,'census.json'),JSON.stringify(summaries,null,2)+'\n')
writeFileSync(join(out,'verification.json'),JSON.stringify(verification,null,2)+'\n')
console.log(JSON.stringify({records:records.length,profiled:comparisons.length,allVerdictsMatch:verification.allVerdictsMatch,allCountedWorkMatches:verification.allCountedWorkMatches,replayFiles:replay.length}))
