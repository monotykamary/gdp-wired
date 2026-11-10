// Static reduction of the raw T1 receipt. It never calls the prover.
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
const [file,out]=process.argv.slice(2)
if(!file||!out)throw new Error('LOG OUTPUT required')
const rows=readFileSync(file,'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l))
const canonical=rows.find(r=>r.test==='T1-canonical'),diagnostic=rows.find(r=>r.diagnostic)
const family=rows.filter(r=>r.mode==='phase-census')
if(!canonical||!diagnostic||family.length!==5)throw new Error('incomplete T1 receipt')
const cutTime=(b:any)=>Object.values(b as Record<string,Record<string,number>>).reduce((n,r)=>n+(r.admission??0)+(r.transport??0),0)
const laws=family.map(r=>{
 const p=r.phases,b=r.t1.buckets,remaining=p.other+p.search+p.proposals
 const selected=Object.fromEntries(['other','search','proposals'].map(k=>[k,b[k]??{}]))
 const admissionTransport=cutTime(selected),broadAdmissionTransport=cutTime(b),wallMinusCounted=r.wallMs-r.countedUnits
 const split={admissionTransport,ordinarySearch:p.search-cutTime({search:b.search??{}}),legacyProposals:p.proposals-cutTime({proposals:b.proposals??{}}),otherConstruction:p.other-cutTime({other:b.other??{}})}
 writeFileSync(join(out,r.law.startsWith('Inv*')?'Invstar.json':r.law.split(':')[0].replaceAll(' ','-')+'.json'),JSON.stringify(r)+'\n')
 return {law:r.law,checked:r.checked,wallMs:r.wallMs,countedUnits:r.countedUnits,phases:p,remaining,split,remainingShare:admissionTransport/remaining,broadAdmissionTransport,wallMinusCounted,broadUpperBoundShare:broadAdmissionTransport/wallMinusCounted,admissionCalls:r.t1.sites['core/count-recovery/conditional-cuts.ts:admitConditionalCut']??null,checks:r.t1.checks}
})
const final=diagnostic.closureSteps.findLast((r:any)=>r.stage==='closure-complete'),admission=canonical.sites['core/count-recovery/conditional-cuts.ts:admitConditionalCut'],loop=canonical.sites['admitCut.per-atom']
const summary={test:'T1',pass:laws.filter(r=>r.law.startsWith('Inv2973')||r.law.startsWith('Inv*')).every(r=>r.remainingShare>=0.5),canonical:{checked:diagnostic.conditionalChecked,cuts:final.cuts,wallMs:diagnostic.wallMs,countedUnits:final.total,wallMinusCounted:diagnostic.wallMs-final.total,admissionMs:admission.wallMs,admissionCalls:admission.calls,admissionPerCut:admission.wallMs/admission.calls,perAtomMs:loop.wallMs,perAtomUncountedShare:loop.wallMs/(diagnostic.wallMs-final.total),admissionUncountedShare:admission.wallMs/(diagnostic.wallMs-final.total),detail:canonical},laws}
writeFileSync(join(out,'results.json'),JSON.stringify(summary,null,2)+'\n')
console.log(JSON.stringify({test:summary.test,pass:summary.pass,canonical:{...summary.canonical,detail:undefined},laws:laws.filter(r=>r.law.startsWith('Inv2973')||r.law.startsWith('Inv*'))}))
