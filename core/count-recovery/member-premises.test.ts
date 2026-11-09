import {expect,test} from 'bun:test'
import {type C,type Machine,all,any,get,ite,n,not,same,x} from '../machine.ts'
import {type CountCert,type CountDecl,assumed,checkMC,mcGoal,substC} from '../../kernel/kernel.ts'
import {clock,grow} from '../../kernel/prove.ts'
import {independentCountInstances} from '../count-focused.ts'
import {admitMemberWitnesses,instantiateMemberPremises,memberPremiseState} from './member-premises.ts'
function fixture(prefix='z_',width=17){
 const name=(s:string)=>prefix+s,k=x(name('member')),actor=x(name('actor')),other=x(name('other')),parcel=get(name('Parcel'),k),cell=(map:string,at=k)=>get(name(map),at)
 const flag=(c:C):C=>({op:'all',key:name('member'),c:any(not(same(parcel,n(1))),c)})
 const m:Machine={name:'renamed',params:[],inputs:[],inputMaps:[name('Parcel')],state:{[name('actor')]:n(0),[name('other')]:n(0)},maps:{[name('Rows')]:0,[name('Epoch')]:0},step:{flags:{[name('view')]:flag(same(cell('Rows'),n(1))),[name('aligned')]:flag(same(cell('Epoch'),cell('Epoch',actor)))}}}
 const ds:CountDecl[]=[{map:name('Incoming'),j:name('row'),key:name('member'),below:n(width),body:ite(same(parcel,n(1)),n(1),n(0))},{map:name('Allowed'),j:name('row'),key:name('member'),below:n(width),body:ite(all(same(cell('Rows'),n(1)),{op:'<=' as const,a:cell('Epoch'),b:cell('Epoch',other)}),n(1),n(0))}]
 const cert={reads:[['input',name('Incoming'),n(0)],['allowed',name('Allowed'),n(0)]] as CountCert['reads'],insts:[] as CountCert['insts']},law={name:name('generated-bound'),forall:name('bound'),holds:{op:'<=' as const,a:cell('Epoch',x(name('bound'))),b:cell('Epoch',other)}}
 return {name,m,ds,cert,law,actor,other}
}
for(const prefix of ['alpha_','other_'])test('ordinary admission and source tuples use declarations, not names or width '+prefix,()=>{
 const f=fixture(prefix,prefix==='alpha_'?17:9),state=memberPremiseState([f.m,[f.law]]),before=JSON.stringify(f)
 const p=admitMemberWitnesses(f.m,f.ds,f.cert,state,10)
 expect(p.hints).toHaveLength(1);expect(p.cert.insts).toHaveLength(1)
 const out=instantiateMemberPremises(f.m,[f.law],{},f.ds,p.hints,state,64)
 expect(out.at['?'+f.name('view')]).toEqual([x(p.cert.insts[0]!.wit)])
 expect(out.at['?'+f.name('aligned')]).toEqual([x(p.cert.insts[0]!.wit)])
 expect(out.at[f.law.name]).toContainEqual(f.actor)
 expect(instantiateMemberPremises(f.m,[f.law],out.at,f.ds,p.hints,state,64).at).toBe(out.at)
 expect(JSON.stringify(f)).toBe(before)
 const again=admitMemberWitnesses(f.m,f.ds,f.cert,state,10)
 expect(again.cert.insts[0]!.wit).toBe(p.cert.insts[0]!.wit)
})
test('the emitted ordinary witness is proved from actual instantiated premises',()=>{
 const f=fixture(),state=memberPremiseState([f.m,[f.law]]),p=admitMemberWitnesses(f.m,f.ds,f.cert,state,10),out=instantiateMemberPremises(f.m,[f.law],{},f.ds,p.hints,state,64)
 const wit=x(p.cert.insts[0]!.wit),flags=Object.entries(f.m.step.flags!).flatMap(([name,q])=>q.op==='all'&&(out.at['?'+name]??[]).some(t=>JSON.stringify(t)===JSON.stringify(wit))?[substC(q.c,{vars:{[q.key]:wit},maps:{},flags:{}})]:[]),claim:C={op:'<=',a:get(f.name('Incoming'),n(0)),b:get(f.name('Allowed'),n(0))},hyps=[...assumed([f.law],out.at),...flags,not(claim)],g=mcGoal(hyps,f.ds,p.cert)!
 const r=grow(g,new Map(),{nodes:0,until:clock()+1000});expect('tree'in r).toBe(true)
 if('tree'in r)expect(checkMC(hyps,f.ds,{...p.cert,tree:r.tree})).toBe(true)
 const consistent=mcGoal([...assumed([f.law],out.at),...flags],f.ds,p.cert)!
 expect('tree'in grow(consistent,new Map(),{nodes:0,until:clock()+1000})).toBe(false)
 const missing=mcGoal([...flags,not(claim)],f.ds,p.cert)!
 expect('tree'in grow(missing,new Map(),{nodes:0,until:clock()+1000})).toBe(false)
})
test('member witnesses can instantiate fields, never a count-read coordinate',()=>{
 const f=fixture(),state=memberPremiseState(f.m),p=admitMemberWitnesses(f.m,f.ds,f.cert,state,1),wit=x(p.cert.insts[0]!.wit)
 const counted={name:'counted',forall:'at',holds:same(get(f.name('Allowed'),x('at')),n(0))},field={name:'field',forall:'at',holds:same(get(f.name('Epoch'),x('at')),n(0))},m={...f.m,counts:{[f.name('Allowed')]:{j:'row',key:'k',below:n(17),body:n(1)}}}
 const out=independentCountInstances(m,[counted,field],{},{counted:[wit],field:[wit],'?view':[wit]},[p.cert.insts[0]!.wit])!
 expect(out.counted).toBeUndefined();expect(out.field).toEqual([wit]);expect(out['?view']).toEqual([wit])
})
test('caps, absent facts and exhausted work do not manufacture premises',()=>{
 const f=fixture(),state=memberPremiseState(f.m)
 expect(admitMemberWitnesses(f.m,f.ds,f.cert,state,0).cert).toBe(f.cert)
 expect(admitMemberWitnesses(f.m,f.ds,f.cert,state,10,()=>false).hints).toHaveLength(0)
 const p=admitMemberWitnesses(f.m,f.ds,f.cert,state,1)
 const out=instantiateMemberPremises(f.m,[f.law],{},f.ds,p.hints,state,1)
 expect(out.added).toHaveLength(1)
 const stopped=instantiateMemberPremises(f.m,[f.law],out.at,f.ds,p.hints,state,64,()=>false)
 expect(stopped.at).toBe(out.at)
 delete f.m.step.flags![f.name('view')]
 expect(admitMemberWitnesses(f.m,f.ds,f.cert,memberPremiseState(f.m),10).hints).toHaveLength(0)
})
test('existing caller names cannot be captured by a fresh member witness',()=>{
 const f=fixture(),state=memberPremiseState({nested:x('member$0')}),p=admitMemberWitnesses(f.m,f.ds,f.cert,state,1)
 expect(p.cert.insts[0]!.wit).not.toBe('member$0')
})
