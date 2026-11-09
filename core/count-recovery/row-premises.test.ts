import {expect,test} from 'bun:test'
import {type C,type Law,type Machine,any,get,n,not,same,tup,x} from '../machine.ts'
import {checkMC,countedObligations,mcGoal} from '../../kernel/kernel.ts'
import {clock,grow} from '../../kernel/prove.ts'
import {instantiateRowPremises} from './row-premises.ts'

function fixture(prefix='r_'){
 const name=(s:string)=>prefix+s,a=x(name('a')),b=x(name('b')),c=x(name('column')),source=x(name('source'))
 const epoch=(at:typeof a)=>get(name('epoch'),at),cell=(row:typeof a)=>get(name('cells'),tup(row,c))
 const holds:C=any(not(same(epoch(a),epoch(b))),same(cell(a),cell(b)))
 const target:Law={name:name('agreement'),forall:name('a'),keys:[name('b'),name('column')],holds}
 const field:Law={name:name('epoch nonnegative'),forall:name('a'),holds:{op:'<=',a:n(0),b:epoch(a)}}
 const counted:Law={name:name('count bound'),forall:name('a'),holds:{op:'<=',a:n(0),b:get(name('count'),a)}}
 const m:Machine={name:'renamed',params:[],inputs:[name('source')],state:{},maps:{[name('epoch')]:0,[name('cells')]:0},counts:{[name('count')]:{j:name('row'),key:name('member'),below:n(11),body:n(1)}},step:{}}
 const own=[x(name('a')+'#'),b,c],laws=[field,counted,target]
 return {name,target,field,counted,m,own,source,laws}
}
for(const prefix of ['alpha_','beta_'])test('source row premises preserve the symbolic column and declared laws '+prefix,()=>{
 const f=fixture(prefix),at={},before=JSON.stringify(f)
 const result=instantiateRowPremises(f.m,f.laws,f.target,at,f.own,[f.source],64)
 expect(result.at[f.target.name]!.slice(0,3)).toEqual(f.own)
 const rowTuples=result.added.filter(p=>p.law===f.target.name)
 expect(rowTuples).toHaveLength(4)
 expect(rowTuples.every(p=>JSON.stringify(p.tuple[2])===JSON.stringify(f.own[2]))).toBe(true)
 expect(result.at[f.counted.name]).toBeUndefined()
 expect(result.added.every(p=>f.laws.some(l=>l.name===p.law))).toBe(true)
 expect(at).toEqual({});expect(JSON.stringify(f)).toBe(before)
 expect(instantiateRowPremises(f.m,f.laws,f.target,result.at,f.own,[f.source],64).at).toBe(result.at)
})
test('row proposals obey shared room, four tuples per source and exhausted work',()=>{
 const f=fixture(),at={}
 expect(instantiateRowPremises(f.m,f.laws,f.target,at,f.own,[f.source],0).at).toBe(at)
 expect(instantiateRowPremises(f.m,f.laws,f.target,at,f.own,[f.source],64,()=>false).at).toBe(at)
 expect(instantiateRowPremises(f.m,f.laws,f.target,at,f.own,[f.source],2).added).toHaveLength(2)
 const result=instantiateRowPremises(f.m,f.laws,f.target,at,f.own,[f.source],64)
 for(const law of f.laws)expect((result.at[law.name]?.length??0)/(1+(law.keys?.length??0))).toBeLessThanOrEqual(4)
 expect(instantiateRowPremises(f.m,f.laws,f.target,at,f.own.slice(0,2),[f.source],64).at).toBe(at)
 expect(instantiateRowPremises(f.m,[f.field],f.target,at,f.own,[f.source],64).at).toBe(at)
})
test('existing premises, not trusted facts, prove an unchanged row relation',()=>{
 const f=fixture(),p=instantiateRowPremises(f.m,f.laws,f.target,{},f.own,[f.source],64)
 const obligations=countedObligations(f.m,f.laws,{[f.target.name]:p.at},f.laws.indexOf(f.target))
 for(const {goal,decls} of obligations){
  const cert={reads:[],insts:[]},g=mcGoal(goal.hyps,decls,cert)!
  const r=grow(g,new Map(),{nodes:0,until:clock()+1000})
  expect('tree'in r).toBe(true)
  if('tree'in r)expect(checkMC(goal.hyps,decls,{...cert,tree:r.tree})).toBe(true)
 }
})
