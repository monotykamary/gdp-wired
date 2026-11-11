import {expect,test} from 'bun:test'
import {type CountCert,type CountDecl,checkMC,mcGoal,canon,framePath} from '../kernel/kernel.ts'
import {clock,fullRate,counted,rowsAt,grow} from '../kernel/prove.ts'
import {n,x,same,get} from './machine.ts'
import {countCertificateSize,dedupeCountInstances,minimizeCountCertificate} from './count-certificate-minimize.ts'
const cert=(tree:CountCert['tree']):CountCert=>({reads:[],insts:[],tree})
test('independent leaf lifts at its parent; missing split rows do not',()=>counted(fullRate,()=>{
 const hyps=[{op:'<=' as const,a:n(1),b:n(0)}],goal=mcGoal(hyps,[],cert({leaf:[]}))!,rows=rowsAt(goal,new Map()),i=rows.findIndex(r=>Object.keys(r.lin).every(k=>k==='1')&&(r.lin['1']??0)>0)
 expect(i).toBeGreaterThanOrEqual(0)
 const split={q:1},leaf=(holds:boolean)=>({leaf:[{kind:'input' as const,index:rowsAt(goal,new Map([[canon(split),{lin:split,holds}]])).findIndex(r=>Object.keys(r.lin).every(k=>k==='1')&&(r.lin['1']??0)>0)}]})
 const source=cert({split,yes:leaf(true),no:leaf(false)})
 expect(checkMC(hyps,[],source)).toBe(true)
 const saved=JSON.stringify(source),out=minimizeCountCertificate(hyps,[],source,clock()+1000)
 expect(out.stats.after.leaves).toBe(1);expect(checkMC(hyps,[],out.cert)).toBe(true);expect(JSON.stringify(source)).toBe(saved)
 const nonProof=minimizeCountCertificate([],[],source,clock()+1000)
 expect(checkMC([],[],nonProof.cert)).toBe(false)
}))
test('frame intersection must still pass frameOk and exact rows are remapped',()=>counted(fullRate,()=>{
 const body={op:'if' as const,c:same(x('mode'),n(0)),then:n(1),else:n(0)},decls:CountDecl[]=[{map:'a',j:'j',key:'k',below:n(2),body},{map:'b',j:'j',key:'k',below:n(2),body}]
 const hyps=[{op:'<' as const,a:get('a',n(0)),b:get('b',n(0))}]
 const source:CountCert={reads:[['ra','a',n(0)],['rb','b',n(0)]],insts:[],tree:{leaf:[]},frames:[{post:'ra',pre:'rb',when:[]},{post:'ra',pre:'rb',when:[]}]}
 const goal=mcGoal(hyps,decls,source)!,proof=grow(goal,framePath(source.frames!,[],new Map()),{nodes:0,until:clock()+1000})
 expect('tree'in proof).toBe(true);if(!('tree'in proof))return
 source.tree=proof.tree;expect(checkMC(hyps,decls,source)).toBe(true)
 const out=minimizeCountCertificate(hyps,decls,source,clock()+1000,{lift:false})
 expect(out.cert.frames).toHaveLength(1);expect(out.cert.frames![0]!.when).toEqual([])
 expect(checkMC(hyps,decls,out.cert)).toBe(true)
 const unequal=[decls[0]!,{...decls[1]!,body:n(1)}]
 const blocked=minimizeCountCertificate(hyps,unequal,source,clock()+1000,{lift:false})
 expect(blocked.cert.frames).toHaveLength(2)
}))
test('conditional frames merge only at their valid common guard',()=>counted(fullRate,()=>{
 const m={mode:1},nm={mode:-1},q={q:1},nq={q:-1,'1':1}
 const decls:CountDecl[]=[{map:'a',j:'j',key:'k',below:n(2),body:{op:'if',c:same(x('mode'),n(0)),then:n(1),else:n(0)}},{map:'b',j:'j',key:'k',below:n(2),body:n(1)}]
 const hyps=[same(x('mode'),n(0)),{op:'<' as const,a:get('a',n(0)),b:get('b',n(0))}]
 const source:CountCert={reads:[['ra','a',n(0)],['rb','b',n(0)]],insts:[],tree:{leaf:[]},frames:[{post:'ra',pre:'rb',when:[m,nm,q]},{post:'ra',pre:'rb',when:[m,nm,nq]}]}
 const goal=mcGoal(hyps,decls,source)!
 const branch=(decisions:[typeof m|typeof q,boolean][])=>new Map(decisions.map(([lin,holds])=>[canon(lin),{lin,holds}]))
 const leaf=(decisions:[typeof m|typeof q,boolean][])=>{const proof=grow(goal,framePath(source.frames!,[],branch(decisions)),{nodes:0,until:clock()+1000});if(!('tree'in proof))throw Error('conditional fixture did not prove');return proof.tree}
 source.tree={split:m,no:leaf([[m,false]]),yes:{split:nm,no:leaf([[m,true],[nm,false]]),yes:{split:q,yes:leaf([[m,true],[nm,true],[q,true]]),no:leaf([[m,true],[nm,true],[q,false]])}}}
 expect(checkMC(hyps,decls,source)).toBe(true)
 const out=minimizeCountCertificate(hyps,decls,source,clock()+1000,{lift:false})
 expect(out.cert.frames).toHaveLength(1);expect(out.cert.frames![0]!.when).toEqual([m,nm]);expect(checkMC(hyps,decls,out.cert)).toBe(true)
}))
test('duplicate formulas are removed without dropping unknown flag instances',()=>{
 const law={name:'a',forall:'v',holds:same(x('v'),n(0))},other={...law,name:'b'},input={a:[n(1),n(1)],b:[n(1),n(2)],'?flag':[n(4)]},before=JSON.stringify(input)
 const result=dedupeCountInstances([law,other],[],input)
 expect(result.instances).toEqual({a:[n(1)],b:[n(2)],'?flag':[n(4)]});expect(result.removed).toHaveLength(2);expect(JSON.stringify(input)).toBe(before)
})
test('shared acyclic proof objects count each occurrence',()=>{
 const leaf={leaf:[]},source=cert({split:{q:1},yes:leaf,no:leaf})
 expect(countCertificateSize(source).leaves).toBe(2)
})
test('lifting remaps appended products and squares',()=>counted(fullRate,()=>{
 const hyps=[{op:'<=' as const,a:n(1),b:n(0)},{op:'<=' as const,a:n(0),b:n(1)}],goal=mcGoal(hyps,[],cert({leaf:[]}))!,split={q:1}
 const leaf=(holds:boolean)=>{const rows=rowsAt(goal,new Map([[canon(split),{lin:split,holds}]])),positive=rows.findIndex(r=>canon(r.lin)==='1:1'),negative=rows.findIndex(r=>canon(r.lin)==='1:-1');return {leaf:[{kind:'input' as const,index:rows.length+1}],squares:[{q:1}],products:[[positive,negative] as [number,number]]}}
 const source=cert({split,yes:leaf(true),no:leaf(false)})
 expect(checkMC(hyps,[],source)).toBe(true)
 const out=minimizeCountCertificate(hyps,[],source,clock()+1000)
 expect(out.stats.after.leaves).toBe(1);expect(checkMC(hyps,[],out.cert)).toBe(true)
}))
test('an expired minimisation preserves the original certificate',()=>{
 const original=cert({leaf:[]}),out=minimizeCountCertificate([],[],original,clock()-1)
 expect(out.cert).toBe(original);expect(out.stats.aborted).toBe(true);expect(countCertificateSize(original).leaves).toBe(1)
})
