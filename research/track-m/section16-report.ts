// Existing receipts only: no solver or proof imports.
import {readFileSync,writeFileSync,mkdtempSync} from 'node:fs'
import {join} from 'node:path'
import {homedir} from 'node:os'
import {strict as assert} from 'node:assert'
const dir=process.argv[2];if(!dir)throw new Error('CENSUS required')
const c=JSON.parse(readFileSync(join(dir,'census.json'),'utf8')),catalog=JSON.parse(readFileSync(join(dir,'lemma-catalog.json'),'utf8'))
const law=(name:string)=>name?.startsWith('Inv2973:')?'Inv2973':name?.startsWith('Inv*:')?'Inv*':undefined
const primary=c.profiles.filter((p:any)=>p.file.startsWith('section15-t12-v3/receipts.br!')).map((p:any)=>{
 const helper=(fn:string)=>p.sites.filter((s:any)=>s.fn===fn).reduce((n:number,s:any)=>n+s.exclusive,0)
 const fieldUnits=helper('fieldBoundLemmas'),frameUnits=helper('frameLemmas')
 assert.equal(p.helperEvents,0)
 return {law:law(p.law),op:p.op,total:p.units,fieldUnits,frameUnits,helperUnits:fieldUnits+frameUnits,otherUnits:p.units-fieldUnits-frameUnits,provedLemmaInventory:null,perLemmaUnits:null,opIndependentOverlap:null,oncePerLawRemainingUnits:null}
})
assert.equal(primary.length,3)
const totals=[...new Set(primary.map((r:any)=>r.law))].map(name=>{const rows=primary.filter((r:any)=>r.law===name),sum=(key:string)=>rows.reduce((s:number,r:any)=>s+r[key],0);return {law:name,coveredOps:rows.map((r:any)=>r.op),observedOpSubtotal:sum('total'),fieldUnits:sum('fieldUnits'),frameUnits:sum('frameUnits'),remainingIfAllHelperWorkWereFree:sum('otherUnits'),remainingOncePerLaw:null,justifiedReusableSavings:null}})
const historical=catalog.normalized.flatMap((g:any)=>{
 const occurrences=g.occurrences.filter((r:any)=>law(r.law));if(!occurrences.length)return []
 const keys=[...new Set(occurrences.map((r:any)=>JSON.stringify([law(r.law),r.op])))],coverage=keys.map(k=>{const [name,op]=JSON.parse(k as string),rows=occurrences.filter((r:any)=>law(r.law)===name&&r.op===op),deltas=rows.flatMap((r:any)=>r.recordedClockDelta===null?[]:[r.recordedClockDelta]);return {law:name,op,positiveRecords:rows.length,checkedRecords:rows.filter((r:any)=>r.checked).length,deferredRecords:rows.filter((r:any)=>r.deferred).length,recordedClockDeltaRange:deltas.length?[Math.min(...deltas),Math.max(...deltas)]:null,countedUnits:null,examples:rows.slice(0,2).map((r:any)=>({file:r.file,path:r.path,receipt:r.receipt}))}})
 return [{id:'F'+(catalog.normalized.indexOf(g)+1),statement:g.text,mentions:g.mentions,proofScopeAvailable:false,rootLiftProven:false,coverage}]
})
const byLaw=Object.fromEntries(['Inv2973','Inv*'].map(name=>[name,historical.filter((g:any)=>g.coverage.some((r:any)=>r.law===name)).map((g:any)=>g.id)])),crossLawStatements=historical.filter((g:any)=>g.coverage.some((r:any)=>r.law==='Inv2973')&&g.coverage.some((r:any)=>r.law==='Inv*')).map((g:any)=>g.id)
const result={receiptOnly:true,policyChanged:false,solverInvoked:false,coverage:{archives:c.archives.length,manifestVerified:c.archives.filter((a:any)=>a.verified).length,parsedArchiveErrors:c.failures,positiveRecordsIncludingDuplicates:c.positiveEvents.length,unresolvedIndexedFrameRecords:catalog.unresolved.filter((r:any)=>r.stage==='frame-lemma').length},primary,totals,historical,syntacticHistoricalOverlap:{byLaw,crossLawStatements,warning:'Statement overlap among positive historical records, not checked op-independent proof overlap. Repeated logs and tails are not separate measurements.'},conclusion:'T-12 drops per-helper events. Neither its actual per-lemma inventory nor once-per-law reusable cost can be reconstructed. Null means unavailable, not zero.'}
const out=mkdtempSync(join(homedir(),'track-m-section16-report-'));writeFileSync(join(out,'summary.json'),JSON.stringify(result,null,2)+'\n')
console.log(JSON.stringify({out,primary,totals,statements:historical.length,crossLawStatements}))
const p=Bun.spawn(['bun','research/track-m/pack-section10-archive.ts',join(out,'summary.json')],{stdout:'inherit',stderr:'inherit'});if(await p.exited)throw new Error('packing failed')
