import {expect,test} from 'bun:test'
import {type C,type Machine,all,any,get,ite,less,n,not,same,x} from '../machine.ts'
import {type CountCert,type CountDecl,checkMC,mcGoal,substC} from '../../kernel/kernel.ts'
import {clock,grow} from '../../kernel/prove.ts'
import {candidateWork,grammarPool} from '../count-support.ts'
import {memberInclusions,preferMemberInclusions} from './member-inclusions.ts'
function fixture(prefix=''){
 const s=(v:string)=>prefix+v,k=x(s('k')),actor=x(s('actor')),other=x(s('other')),q=get(s('Parcel'),k),cell=(map:string,at= k)=>get(s(map),at)
 const flag=(c:C):C=>({op:'all',key:s('k'),c:any(not(same(q,n(1))),c)})
 const m:Machine={name:'arbitrary',params:[],inputs:[s('actor'),s('other')],inputMaps:[s('Parcel')],state:{},maps:{[s('Rows')]:0,[s('Epoch')]:0,[s('Version')]:0},step:{flags:{view:flag(same(cell('Rows'),n(1))),aligned:flag(all(same(cell('Epoch'),cell('Epoch',actor)),same(cell('Version',actor),cell('Version'))))}}}
 const base={j:s('unused'),key:s('k'),below:n(12)},ds:CountDecl[]=[{...base,map:s('Incoming'),body:q},{...base,map:s('Eligible'),body:ite(all(same(cell('Rows'),n(1)),less(cell('Epoch'),cell('Epoch',other)),not(any(less(cell('Epoch',actor),cell('Epoch')),all(same(cell('Epoch',actor),cell('Epoch')),less(cell('Version',actor),cell('Version')))))),n(1),n(0))}]
 const reads:CountCert['reads']=[['input',s('Incoming'),n(0)],['eligible',s('Eligible'),n(0)]]
 return {m,ds,reads,cell,actor,other,s,run:()=>memberInclusions(m,ds,reads)}
}
for(const prefix of ['', 'renamed_'])test('equality consequents discharge reflexive bodies and retain scalar residue '+prefix,()=>{
 const f=fixture(prefix),before=JSON.stringify([f.m,f.ds,f.reads])
 expect(f.run()).toEqual([{positive:'input',negative:'eligible',carried:f.s('Parcel'),below:n(12),guards:[less(f.cell('Epoch',f.actor),f.cell('Epoch',f.other))]}])
 expect(JSON.stringify([f.m,f.ds,f.reads])).toBe(before)
})
test('unknown membership is not treated as implied',()=>{const f=fixture();delete f.m.step.flags!.view;expect(f.run()).toEqual([])})
function upperBoundFixture(){
 const f=fixture(),body=f.ds[1]!.body
 if(body.op!=='if'||body.c.op!=='and')throw Error('fixture')
 const notNewer=body.c.xs[2]!
 f.m.step.flags!.aligned={op:'all',key:'k',c:any(not(same(get('Parcel',x('k')),n(1))),all({op:'<=',a:get('Epoch',x('k')),b:get('Epoch',x('actor'))},notNewer))}
 return f
}
test('member upper bounds propose sufficient scalar guards without equality anchors',()=>{
 const f=upperBoundFixture(),before=JSON.stringify([f.m,f.ds,f.reads])
 expect(f.run()).toEqual([{positive:'input',negative:'eligible',carried:'Parcel',below:n(12),guards:[less(get('Epoch',x('actor')),get('Epoch',x('other')))]}])
 expect(JSON.stringify([f.m,f.ds,f.reads])).toBe(before)
})
for(const strict of [false,true])for(const targetStrict of [false,true])test(`upper-bound guards preserve strictness: source ${strict?'strict':'inclusive'}, target ${targetStrict?'strict':'inclusive'}`,()=>{
 const f=upperBoundFixture(),q=f.m.step.flags!.aligned,body=f.ds[1]!.body
 if(!q||q.op!=='all'||q.c.op!=='or'||q.c.xs[1]?.op!=='and'||body.op!=='if'||body.c.op!=='and')throw Error('fixture')
 q.c.xs[1].xs[0]={op:strict?'<':'<=',a:get('Epoch',x('k')),b:get('Epoch',x('actor'))}
 body.c.xs[1]={op:targetStrict?'<':'<=',a:get('Epoch',x('k')),b:get('Epoch',x('other'))}
 expect(f.run()[0]!.guards).toEqual([{op:strict||!targetStrict?'<=':'<',a:get('Epoch',x('actor')),b:get('Epoch',x('other'))}])
})
test('strict carried-member bounds prove equality at the target boundary only with the original flags',()=>{
 const f=upperBoundFixture(),q=f.m.step.flags!.aligned
 if(!q||q.op!=='all'||q.c.op!=='or'||q.c.xs[1]?.op!=='and')throw Error('fixture')
 q.c.xs[1].xs[0]=less(get('Epoch',x('k')),get('Epoch',x('actor')))
 const boundary=same(get('Epoch',x('actor')),get('Epoch',x('other'))),claim:C={op:'<=',a:get('Incoming',n(0)),b:get('Eligible',n(0))}
 const initial={name:'strict member boundary',hyps:[boundary,not(claim)]},pool=grammarPool(initial,f.ds,100,candidateWork(),true,f.m),picked=preferMemberInclusions(f.m,f.ds,pool.full,{...pool.full,insts:[],picks:[]})
 expect(f.run()[0]!.guards).toEqual([{op:'<=',a:get('Epoch',x('actor')),b:get('Epoch',x('other'))}])
 expect(picked.insts).toHaveLength(1)
 const wit=x(picked.insts[0]!.wit),member=get('Parcel',wit),booleanMember=any(same(member,n(0)),same(member,n(1))),flagsAt=()=>Object.values(f.m.step.flags!).flatMap(q=>q.op==='all'?[substC(q.c,{vars:{[q.key]:wit},maps:{},flags:{}})]:[])
 const raw=[boundary,booleanMember,...flagsAt(),not(claim)],numeric=mcGoal(raw,f.ds,picked)!,out=grow(numeric,new Map(),{nodes:0,until:clock()+1000})
 expect('tree'in out).toBe(true)
 if('tree'in out){expect(checkMC(raw,f.ds,{...picked,tree:out.tree})).toBe(true);expect(checkMC([boundary,booleanMember,not(claim)],f.ds,{...picked,tree:out.tree})).toBe(false)}
 q.c.xs[1].xs[0]={op:'<=',a:get('Epoch',x('k')),b:get('Epoch',x('actor'))}
 expect('tree'in grow(mcGoal([boundary,booleanMember,...flagsAt(),not(claim)],f.ds,picked)!,new Map(),{nodes:0,until:clock()+1000})).toBe(false)
})
test('an upper bound is not rewritten in a negative comparison',()=>{
 const f=upperBoundFixture()
 f.ds[1]!.body=ite(all(same(get('Rows',x('k')),n(1)),not(less(get('Epoch',x('k')),get('Epoch',x('other'))))),n(1),n(0))
 expect(f.run()).toEqual([])
})
test('upper-bound suggestions still require the scalar guard and checked witness flags',()=>{
 const f=upperBoundFixture(),guard=less(get('Epoch',x('actor')),get('Epoch',x('other'))),claim:C={op:'<=',a:get('Incoming',n(0)),b:get('Eligible',n(0))}
 const initial={name:'bounded-member inclusion',hyps:[guard,not(claim)]},pool=grammarPool(initial,f.ds,100,candidateWork(),true,f.m),picked=preferMemberInclusions(f.m,f.ds,pool.full,{...pool.full,insts:[],picks:[]})
 expect(picked.insts).toHaveLength(1)
 const wit=x(picked.insts[0]!.wit),member=get('Parcel',wit),booleanMember=any(same(member,n(0)),same(member,n(1))),flags=Object.values(f.m.step.flags!).flatMap(q=>q.op==='all'?[substC(q.c,{vars:{[q.key]:wit},maps:{},flags:{}})]:[])
 const raw=[guard,booleanMember,...flags,not(claim)],numeric=mcGoal(raw,f.ds,picked)!
 const out=grow(numeric,new Map(),{nodes:0,until:clock()+1000})
 expect('tree'in out).toBe(true)
 if('tree'in out)expect(checkMC(raw,f.ds,{...picked,tree:out.tree})).toBe(true)
 const unguarded=mcGoal([booleanMember,...flags,not(claim)],f.ds,picked)!
 expect('tree'in grow(unguarded,new Map(),{nodes:0,until:clock()+1000})).toBe(false)
})
test('an inequality is not a substitution',()=>{const f=fixture();f.m.step.flags!.aligned={op:'all',key:'k',c:any(not(same(get('Parcel',x('k')),n(1))),less(get('Epoch',x('k')),get('Epoch',x('actor'))))};expect(f.run()).toEqual([])})
test('different domains cannot form an inclusion',()=>{const f=fixture();f.ds[1]!.below=n(13);expect(f.run()).toEqual([])})
test('another carried map does not supply these member facts',()=>{const f=fixture();f.m.inputMaps=['Unrelated'];expect(f.run()).toEqual([])})
test('a still-member-dependent predicate is not a scalar residue',()=>{const f=fixture();const old=f.ds[1]!.body;if(old.op!=='if')throw new Error('fixture');old.c=all(old.c,less(get('Unknown',x('k')),n(4)));expect(f.run()).toEqual([])})
test('without an equality rewrite, ordinary membership stays with the old family',()=>{const f=fixture();f.ds[1]!.body=ite(same(get('Rows',x('k')),n(1)),n(1),n(0));expect(f.run()).toEqual([])})
test('a discharged equality may yield an unconditional candidate, never an asserted cut',()=>{const f=fixture();f.ds[1]!.body=ite(all(same(get('Rows',x('k')),n(1)),same(get('Epoch',x('k')),get('Epoch',x('actor')))),n(1),n(0));expect(f.run()[0]!.guards).toEqual([])})
test('cyclic input is refused before recursive substitution',()=>{const f=fixture();const c:any={op:'not'};c.x=c;f.m.step.flags!.bad=c;expect(f.run()).toEqual([])})

test('ordinary selection receives an existing guarded inclusion within its unchanged cap',()=>{
 const f=fixture(),noise=Array.from({length:10},(_,i)=>({wit:`old${i}`,unit:0,below:n(12),terms:[[i+1,'eligible']] as [number,string][]})),hit={wit:'existing',unit:0,below:n(12),terms:[[1,'input'],[-1,'eligible']] as [number,string][]}
 const full={reads:f.reads,insts:[...noise,hit]},picked={reads:f.reads,insts:noise},before=JSON.stringify([f.m,f.ds,full,picked]),out=preferMemberInclusions(f.m,f.ds,full,picked)
 expect(out.insts).toHaveLength(10)
 expect(out.insts[0]).toBe(hit)
 expect(out.insts.every(q=>full.insts.includes(q))).toBe(true)
 expect(JSON.stringify([f.m,f.ds,full,picked])).toBe(before)
})

test('selection cannot manufacture a missing instance or borrow unrelated member flags',()=>{
 const f=fixture(),hit={wit:'existing',unit:0,below:n(12),terms:[[1,'input'],[-1,'eligible']] as [number,string][]},full={reads:f.reads,insts:[hit]},picked={reads:f.reads,insts:[]}
 expect(preferMemberInclusions(f.m,f.ds,{...full,insts:[]},picked)).toBe(picked)
 delete f.m.step.flags!.view
 expect(preferMemberInclusions(f.m,f.ds,full,picked)).toBe(picked)
})

test('selection respects an explicitly smaller cap and does not assert its scalar residue',()=>{
 const f=fixture(),hit={wit:'existing',unit:0,below:n(12),terms:[[1,'input'],[-1,'eligible']] as [number,string][]},full={reads:f.reads,insts:[hit]},picked={reads:f.reads,insts:[]}
 const out=preferMemberInclusions(f.m,f.ds,full,picked,1)
 expect(out).toEqual({reads:f.reads,insts:[hit]})
 expect(Object.keys(out).sort()).toEqual(['insts','reads'])
 expect(preferMemberInclusions(f.m,f.ds,full,picked,0)).toBe(picked)
})

test('initial selection shares its cap with existing picks and respects exhausted proposal work',()=>{
 const f=fixture(),hit={wit:'existing',unit:0,below:n(12),terms:[[1,'input'],[-1,'eligible']] as [number,string][]},picks=Array.from({length:9},()=>['input',[n(0)]]) as NonNullable<CountCert['picks']>,full={reads:f.reads,insts:[hit],picks},picked={reads:f.reads,insts:[],picks}
 const out=preferMemberInclusions(f.m,f.ds,full,picked)
 expect(out.insts).toEqual([hit]);expect(out.picks).toBe(picks)
 expect(out.picks.length+out.insts.length).toBe(10)
 expect(preferMemberInclusions(f.m,f.ds,full,picked,10,()=>false)).toBe(picked)
})

test('the raw lazy pool admits a genuinely missing bound-specialized inclusion with a fresh witness',()=>{
 const f=fixture();f.ds[0]!.below=x(f.ds[0]!.j)
 const goal={name:'specialized bound',hyps:[same(get('Incoming',n(12)),get('Eligible',n(0)))]},before=JSON.stringify([f.m,f.ds,goal])
 const plain=grammarPool(goal,f.ds,100,candidateWork(),true),pool=grammarPool(goal,f.ds,100,candidateWork(),true,f.m)
 const added=pool.added.filter(a=>a.reason==='guarded member inclusion')
 expect(added).toHaveLength(1)
 expect(added[0]!.instance.below).toEqual(n(12))
 expect(Object.keys(added[0]!.instance).sort()).toEqual(['below','terms','unit','wit'])
 expect(pool.full.insts.slice(0,plain.full.insts.length)).toEqual(plain.full.insts)
 expect(pool.freshWitnesses).toBe(true)
 // The legacy unary tuples retain the declaration's uninstantiated bound in
 // this synthetic fixture. Validate the newly admitted instance independently.
 expect(mcGoal(goal.hyps,f.ds,{reads:pool.full.reads,insts:added.map(a=>a.instance)})).toBeDefined()
 expect(JSON.stringify([f.m,f.ds,goal])).toBe(before)
 const capped=grammarPool(goal,f.ds,1,candidateWork(),true,f.m)
 expect(capped.full.insts).toHaveLength(1)
 expect(capped.added.some(a=>a.reason==='guarded member inclusion')).toBe(false)
})

test('an ordinary selected witness proves the conditional inclusion but not its unguarded strengthening',()=>{
 const f=fixture(),claim:C={op:'<=',a:get('Incoming',n(0)),b:get('Eligible',n(0))},guard=less(f.cell('Epoch',f.actor),f.cell('Epoch',f.other))
 const initial={name:'conditional inclusion',hyps:[guard,not(claim)]},pool=grammarPool(initial,f.ds,100,candidateWork(),true,f.m),picked=preferMemberInclusions(f.m,f.ds,pool.full,{...pool.full,insts:[],picks:[]})
 expect(picked.insts).toHaveLength(1)
 const wit=x(picked.insts[0]!.wit),member=get('Parcel',wit),booleanMember=any(same(member,n(0)),same(member,n(1))),flags=Object.values(f.m.step.flags!).flatMap(q=>q.op==='all'?[substC(q.c,{vars:{[q.key]:wit},maps:{},flags:{}})]:[])
 const raw=[guard,booleanMember,...flags,not(claim)],numeric=mcGoal(raw,f.ds,picked)!
 const out=grow(numeric,new Map(),{nodes:0,until:clock()+1000})
 expect('tree'in out).toBe(true)
 if('tree'in out)expect(checkMC(raw,f.ds,{...picked,tree:out.tree})).toBe(true)
 const unguarded=mcGoal([booleanMember,...flags,not(claim)],f.ds,picked)!
 expect('tree'in grow(unguarded,new Map(),{nodes:0,until:clock()+1000})).toBe(false)
})
