// Independent replay of published proof transport and work accounting.
import {readFileSync} from 'node:fs'
import {termColumn,countHyp,countHyps,checkCounted,lemmaPath,canon,check,linear,type Path} from '../../kernel/kernel.ts'
import {countsForReads} from '../../core/count-facts.ts'
import {refuteFast,sub} from '../../core/solver.ts'
import {brokenOf,rowsAt} from '../../kernel/prove.ts'
import {walkLive} from '../../core/count-recovery/live-dependencies.ts'
const [seedFile,packetFile,...resultFiles]=process.argv.slice(2);if(!seedFile||!packetFile)throw new Error('SEEDS PACKET [RESULT...]')
const read=(f:string)=>JSON.parse(readFileSync(f,'utf8')),seed=read(seedFile),p=read(packetFile)
for(const [i,t]of seed.columns.entries())if(termColumn(t)!==`⟦${i}⟧`)throw new Error('column namespace mismatch')
const counts=countsForReads(p.packet.decls,p.cert.reads);if(!counts)throw new Error('counts missing')
const hyps=countHyps(counts,p.cert.insts)
if(JSON.stringify(hyps)!==JSON.stringify(seed.root.hyps.slice(-p.cert.insts.length)))throw new Error('root count hypotheses differ')
for(const x of seed.accepted){
 if(x.lemma.when.length)throw new Error('guarded root fact')
 const good=x.good;if(good.op!=='<=')throw new Error('not a linear comparison')
 const cut=sub(linear(good.a,new Map())!,linear(good.b,new Map())!);if(canon(cut)!==canon(x.lemma.cut))throw new Error('conclusion mismatch')
 for(const i of x.lemma.slice)if(!Number.isInteger(i)||i<0||i>=seed.root.hyps.length)throw new Error('invalid slice')
 const goal={name:'independent-root-audit',hyps:x.lemma.slice.map((i:number)=>seed.root.hyps[i])},path:Path=new Map([[canon(cut),{lin:cut,holds:false}]])
 if(!check(goal,x.lemma.tree,path))throw new Error('root proof rejected: '+x.index)
 if(check(goal,{leaf:[]},path))throw new Error('empty corrupt proof accepted')
 // MC hypotheses may mention universal witnesses. Audit each identity instead
 // with the stronger bare-count rule, rebased onto its sole count axiom.
 const record=seed.records.find((r:any)=>r.index===x.index),hyp=countHyp(counts,record.inst)
 if(!hyp||x.lemma.slice.length!==1||JSON.stringify(goal.hyps)!==JSON.stringify([hyp]))throw new Error('identity depends on non-count premises')
 const standalone={name:'standalone-root-audit',hyps:[{op:'not' as const,x:good},hyp]},rebased={...x.lemma,slice:[1]},closed=refuteFast(rowsAt(standalone,lemmaPath([rebased],new Map())),256)
 if(closed?.kind!=='refuted'||!checkCounted({name:standalone.name,hyps:[{op:'not',x:good}],counts},{insts:[record.inst],lemmas:[rebased],tree:{leaf:closed.steps}}))throw new Error('independent counted root check failed')
}
const close=(a:number,b:number)=>Math.abs(a-b)<1e-6*Math.max(1,Math.abs(a),Math.abs(b)),sum=(xs:any[],field:string)=>xs.reduce((s,x)=>s+x[field],0)
if(!close(sum(seed.records,'units'),seed.units))throw new Error('root units mismatch')
if(seed.lawRoot&&!close(sum(seed.lawRoot.records,'units'),seed.lawRoot.units))throw new Error('additional root units mismatch')
let rootSat=0
for(const r of seed.records.filter((r:any)=>r.outcome==='sat')){
 const hyp=countHyp(counts,r.inst);if(!hyp)throw new Error('missing source count hypothesis')
 const goal={name:'independent-sat-audit',hyps:[{op:'not' as const,x:r.good},hyp]},model={...r.model}
 walkLive(goal.hyps,new Map(),(x:any)=>{if(x.op==='var'&&!Object.hasOwn(model,x.name))model[x.name]=0})
 if(!Object.values(model).every(Number.isSafeInteger)||brokenOf(goal)(model).length)throw new Error('invalid source SAT '+r.index)
 rootSat++
}
const results=resultFiles.map(file=>{const r=read(file);if(!r.productionLocalDeadlines||r.inflightDump)throw new Error('clock/dump control mismatch')
 const ledgerUnits=sum(r.ledger,'units');if(ledgerUnits>r.units+1e-5)throw new Error('ledger exceeds total')
 if(r.closed)throw new Error('closed replay requires a serialized certificate audit')
 const failed=r.firstFailure?.capture,model=failed?.model
 if(model){
  const value=(name:string)=>{const n=model[name]??0;if(!Number.isSafeInteger(n))throw new Error('nonintegral model');return BigInt(n)}
  for(const [,a]of failed.path){let n=0n;for(const [k,z]of Object.entries(a.lin)){if(!Number.isSafeInteger(z))throw new Error('nonintegral path');n+=BigInt(z as number)*(k==='1'?1n:value(k))}if((n<=0n)!==a.holds)throw new Error('path not satisfied')}
  const bound=(e:any):bigint=>{if(e.op==='var')return value(e.name);if(e.op==='const')return BigInt(e.value);if(e.op==='add')return bound(e.a)+bound(e.b);if(e.op==='mul')return BigInt(e.k)*bound(e.a);throw new Error('unsupported exact bound')}
  const violated=failed.pool.filter((index:number)=>{const i=failed.cert.insts[index];return i.terms.reduce((s:bigint,[k,n]:[number,string])=>s+BigInt(k)*value(n),0n)+BigInt(i.unit)*bound(i.below)>0n})
  if(JSON.stringify(violated)!==JSON.stringify(failed.violated))throw new Error('violated set mismatch')
 }
 return {file,op:r.op,seeded:r.seeded,seedCount:r.seedCount,units:r.units,wallMs:r.wallMs,cuts:r.stats.cuts,sourceSat:r.stats.sat,sourceRefuted:r.stats.checkedSources,leaves:sum(r.ledger,'leaves'),outsideActionUnits:r.units-ledgerUnits,firstPath:r.firstFailure?.path,hasModel:!!model,exactPathAndViolatedSet:!!model,violated:failed?.violated??null,reason:r.firstFailure?.reason}
})
console.log(JSON.stringify({audit:'section14',accepted:seed.accepted.length,allProofsRechecked:true,allEmptyMutantsRejected:true,validatedRootSatPoints:rootSat,rootUnits:seed.units,lawRootUnits:seed.lawRoot?.units??0,results},null,2))
