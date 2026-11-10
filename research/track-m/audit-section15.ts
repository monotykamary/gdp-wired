// Independent accounting and exact first-point audit; no solver rerun.
import {readFileSync,writeFileSync,mkdtempSync} from 'node:fs'
import {join} from 'node:path'
import {homedir} from 'node:os'
import {strict as assert} from 'node:assert'
const dir=process.argv[2];if(!dir)throw new Error('INPUT required')
const read=(name:string)=>JSON.parse(readFileSync(join(dir,name),'utf8')),integrity=read('integrity.json')
assert(integrity.kernelIdentical);assert.deepEqual(integrity.changed.toSorted(),['core/count-cases.ts','core/count-focus-proof.ts','core/count-recovery/derivability-closure.ts','core/count-recovery/guard-cases.ts'].toSorted())
const sum=(xs:number[])=>xs.reduce((a,b)=>a+b,0),near=(a:number,b:number)=>Math.abs(a-b)<1e-6*Math.max(1,Math.abs(a),Math.abs(b)),rows:any[]=[]
for(const name of ['overlap-op4','overlap-op0','star-op3']){
 const r=read(name+'-result.json'),frames:any[]=r.trace.frames;assert.equal(r.allowance,5000);assert(!r.error);assert(!r.closed,'a closed result needs a serialized proof audit');assert.equal(r.seedCount,0);assert(r.productionLocalDraws&&!r.inflightDump);assert.deepEqual(r.flags,{cap:true,classes:true,modelFirst:true})
 const nearest=(id:number|undefined,kind:string):any=>{while(id!==undefined){const f=frames[id];if(f.kind===kind)return f;id=f.parent}return undefined}
 assert(near(sum(frames.filter(f=>f.parent===undefined).map(f=>f.units)),r.units));assert(near(sum(frames.map(f=>f.exclusive)),r.units));assert(near(sum(r.ledger.map((x:any)=>x.units))+sum(frames.filter(f=>f.parent===undefined&&f.kind!=='action').map(f=>f.units)),r.units))
 const inside=sum(frames.filter(f=>nearest(f.id,'closure')).map(f=>f.exclusive)),outside=sum(frames.filter(f=>!nearest(f.id,'closure')).map(f=>f.exclusive));assert(near(inside+outside,r.units))
 for(const site of r.sites){const fs=frames.filter(f=>f.kind==='action-site'&&f.meta.site===site.site);assert.equal(fs.length,site.calls);assert(near(sum(fs.map(f=>f.exclusive)),site.exclusive))}
 const outcomes=new Map(r.trace.events.filter((e:any)=>e.kind==='source-result').map((e:any)=>[e.frame,e.outcome])),sourceUnits=sum(frames.filter(f=>f.kind==='source-query'&&outcomes.get(nearest(f.id,'source-attempt')?.id)==='checked').map(f=>f.exclusive));assert(near(sourceUnits,r.checkedSourceQueryUnits))
 const c=r.firstFailure?.capture;let exact=false
 if(c?.model){const value=(n:string)=>{const z=c.model[n]??0;assert(Number.isSafeInteger(z));return BigInt(z)}
  for(const [,a]of c.path){let z=0n;for(const [n,k]of Object.entries(a.lin)){assert(Number.isSafeInteger(k));z+=BigInt(k as number)*(n==='1'?1n:value(n))}assert.equal(z<=0n,a.holds)}
  const bound=(e:any):bigint=>{if(e.op==='var')return value(e.name);if(e.op==='const')return BigInt(e.value);if(e.op==='add')return bound(e.a)+bound(e.b);if(e.op==='mul')return BigInt(e.k)*bound(e.a);throw new Error('unsupported bound')}
  const violated=c.pool.filter((i:number)=>{const q=c.cert.insts[i];return q.terms.reduce((s:bigint,[k,n]:[number,string])=>s+BigInt(k)*value(n),0n)+BigInt(q.unit)*bound(q.below)>0n});assert.deepEqual(violated,c.violated);exact=true
 }
 const kinds=Object.fromEntries([...new Set(frames.map(f=>f.kind))].map(k=>[k,{calls:frames.filter(f=>f.kind===k).length,exclusive:sum(frames.filter(f=>f.kind===k).map(f=>f.exclusive))}]))
 rows.push({name,law:r.law,op:r.op,verdict:r.verdict,units:r.units,wallMs:r.wallMs,insideClosureUnits:inside,outsideClosureUnits:outside,checkedSourceQueryUnits:sourceUnits,checkedSourceAttemptUnits:r.checkedSourceAttemptUnits,stopRuleTriggered:r.stopRuleTriggered,ledger:r.ledger,sites:r.sites,rounds:r.rounds,phases:frames.filter(f=>f.kind==='action'&&f.meta.value===r.op).map(f=>({phase:f.meta.phase,units:f.units})),kinds,firstFailure:c?{reason:r.firstFailure.reason,path:c.path,model:c.model,violated:c.violated}:r.firstFailure,exactFirstPointAudit:exact})
}
assert(rows.find(r=>r.name==='overlap-op4').stopRuleTriggered)
const result={researchOnly:true,allowance:5000,kernelUnchanged:true,ledgerAudit:true,rows,stop:'T-12 op 4 exceeds 2,500 units; no further policy work'}
const out=mkdtempSync(join(homedir(),'track-m-section15-audit-'));writeFileSync(join(out,'summary.json'),JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify({audited:rows.length,exactPoints:rows.filter(r=>r.exactFirstPointAudit).length,summary:join(out,'summary.json')}))
const p=Bun.spawn(['bun','research/track-m/pack-section10-archive.ts',join(out,'summary.json')],{stdout:'inherit',stderr:'inherit'});if(await p.exited)throw new Error('archive failed')
