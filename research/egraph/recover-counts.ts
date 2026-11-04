// Parse existing count rows; accept metadata only after unchanged mcGoal round-trip.
import type {C,E} from '../../core/machine.ts'
import {mcGoal,type Goal,type CountDecl,type CountInst,type MapRead} from '../../kernel/kernel.ts'
import {Meter,Exhausted} from './match.ts'
import {stableKey} from './recover-instances.ts'
type Side={terms:[number,string][],unit:number}
function side(e:E,meter:Meter):Side|undefined{
  meter.tick();if(e.op!=='add'||e.b.op!=='mul')return
  const unit=e.b.k,terms:[number,string][]=[];let tail=e.a
  if(!Number.isSafeInteger(unit)||unit<0)return
  while(tail.op==='add'){
    meter.tick();const head=tail.a;if(head.op!=='mul'||head.a.op!=='var'||!Number.isSafeInteger(head.k)||head.k<0)return
    terms.push([head.k,head.a.name]);tail=tail.b
  }
  if(tail.op!=='const'||tail.value!==0)return
  return {terms,unit}
}
export function parseCountInstance(c:C,meter:Meter):CountInst|undefined{
  meter.tick();if(c.op!=='or'||c.xs.length!==2)return
  const a=c.xs[0]!,b=c.xs[1]!
  if(a.op!=='<='||b.op!=='and'||b.xs.length!==2)return
  const bound=b.xs[0]!;if(bound.op!=='<'||bound.a.op!=='var')return
  const pos=side(a.a,meter),neg=side(a.b,meter)
  if(!pos||!neg||pos.terms.length!==neg.terms.length)return
  if(pos.terms.some((t,i)=>t[1]!==neg.terms[i]![1]))return
  return {wit:bound.a.name,below:bound.b,terms:pos.terms.map(([n,v],i)=>[n-neg.terms[i]![0],v]),unit:pos.unit-neg.unit}
}
function parsePick(c:C,meter:Meter):[string,E[]]|undefined{
  meter.tick();if(c.op!=='or'||c.xs.length!==2)return
  const a=c.xs[0]!,b=c.xs[1]!;if(a.op!=='not'||b.op!=='<='||b.b.op!=='var')return
  let tail=a.x;const keys:E[]=[]
  while(tail.op==='and'){
    meter.tick();if(tail.xs.length!==2)return
    const first=tail.xs[0]!,rest=tail.xs[1]!
    if(first.op!=='<'||rest.op!=='and'||rest.xs.length!==2)return
    keys.push(first.a);tail=rest.xs[1]!
  }
  // Terminal shape and every distinctness test are validated by the round trip.
  return [b.b.name,keys]
}
export function recoverCounts(goal:Goal,decls:CountDecl[],suggestedReads:MapRead[],meter:Meter){
  const originalKeys=goal.hyps.map(c=>stableKey(c,meter)),original=new Set(originalKeys)
  const reads=[...suggestedReads],byName=new Set(reads.map(r=>r[0])),usedRows=new Set<string>()
  if(byName.size!==reads.length)throw Error('duplicate recovered read name')
  const generate=(is:CountInst[],ps:[string,E[]][])=>{
    // One real kernel reconstruction, so each selected declaration is traversed
    // and charged once per batch, not once per proposed row.
    for(const r of reads){const d=decls.find(x=>x.map===r[1]);if(d)stableKey(d,meter)}
    stableKey([reads,is,ps],meter)
    return mcGoal([],decls,{reads,insts:is,picks:ps})
  }
  const readGoal=generate([],[])
  if(!readGoal||readGoal.hyps.length!==reads.length)throw Error('invalid recovered reads')
  const countRows:C[]=[...readGoal.hyps],countRowKeys:string[]=[]
  for(const row of readGoal.hyps){const key=stableKey(row,meter);if(!original.has(key))throw Error('read row absent from original goal');usedRows.add(key);countRowKeys.push(key)}
  const candidates:{inst:CountInst,index:number}[]=[],pickCandidates:{pick:[string,E[]],index:number}[]=[]
  goal.hyps.forEach((row,index)=>{
    meter.tick();const inst=parseCountInstance(row,meter),pick=inst?undefined:parsePick(row,meter)
    if(inst&&inst.terms.every(t=>byName.has(t[1])))candidates.push({inst,index})
    else if(pick&&byName.has(pick[0]))pickCandidates.push({pick,index})
    if(reads.length+candidates.length+pickCandidates.length>512)throw new Exhausted('count metadata record cap')
  })
  const generated=generate(candidates.map(x=>x.inst),pickCandidates.map(x=>x.pick))
  if(!generated||generated.hyps.length!==reads.length+candidates.length+pickCandidates.length)throw Error('count batch reconstruction refused')
  const insts:CountInst[]=[],picks:[string,E[]][]=[]
  pickCandidates.forEach(({pick,index},i)=>{meter.tick();const key=stableKey(generated.hyps[reads.length+i],meter);if(key===originalKeys[index]){picks.push(pick);usedRows.add(key);countRows.push(generated.hyps[reads.length+i]!);countRowKeys.push(key)}})
  candidates.forEach(({inst,index},i)=>{meter.tick();const key=stableKey(generated.hyps[reads.length+pickCandidates.length+i],meter);if(key===originalKeys[index]){insts.push(inst);usedRows.add(key);countRows.push(generated.hyps[reads.length+pickCandidates.length+i]!);countRowKeys.push(key)}})
  return {reads,insts,picks,usedRows,originalKeys,countRows,countRowKeys}
}
