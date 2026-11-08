import {expect,test} from 'bun:test'
import {type Machine,all,any,atMost,get,ite,less,minus,n,not,plus,same,times,x} from '../machine.ts'
import {type CountCert,type Path,canon,check,mcGoal} from '../../kernel/kernel.ts'
import {clock,grow,widen} from '../../kernel/prove.ts'
import {fieldOnlyGoal} from './field-only.ts'
import {fieldCase} from './field-case.ts'
const m:Machine={name:'field projection',params:[],inputs:[],state:{},counts:{Rows:{j:'r',key:'k',below:n(2),body:n(1)}},step:{}}
const cert:Pick<CountCert,'reads'|'insts'>={reads:[['amount','Rows',n(0)]],insts:[]}
test('field projection only weakens premises and transports a checked proof',()=>{
 const field=atMost(x('value'),n(1)),count=atMost(get('Rows',n(0)),n(2)),g={name:'field',hyps:[all(field,count),{op:'not' as const,x:field}]}
 const small=fieldOnlyGoal(g,m,cert)!
 expect(small.hyps[0]).toEqual(all(field))
 const result=grow(small,new Map(),{nodes:0,until:clock()+1000})
 expect('tree'in result).toBe(true)
 if('tree'in result){const tree=widen(small,g,result.tree);expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)}
})
test('field projection uses the source conclusion before appended count bindings',()=>{
 const field=atMost(x('value'),n(1)),claim={op:'not' as const,x:field},ds=[{map:'Rows',...m.counts!.Rows!}]
 const goal=mcGoal([field,claim],ds,cert)!
 const projected=fieldOnlyGoal(goal,m,cert,claim)
 expect(projected).toBeDefined()
 expect(projected?.hyps.at(-1)).toBe(claim)
})
test('packed copy fields reconstruct their equal-key core under row equalities',()=>{
 const m:Machine={name:'packed copy',params:['size'],inputs:['i'],state:{},maps:{Config:0},step:{}},a=x('a'),b=x('b'),i=x('i'),c=x('c'),size=x('size'),index=(r:typeof a)=>plus(times(64,r),c)
 const cell=(r:typeof a)=>{const key=index(r),inside=all(atMost(times(64,i),key),less(key,plus(times(64,i),n(64))));return ite(any(all(inside,same(get('Config',minus(key,times(64,i))),n(1))),all(not(inside),same(get('Config',key),n(1)))),n(1),n(0))}
 const claim=not(any(not(all(less(a,size),less(b,size),less(c,size))),same(cell(a),cell(b)))),g={name:'packed',hyps:[all(atMost(n(1),size),atMost(size,n(64))),claim]},path:Path=new Map()
 for(const lin of [{a:1,i:-1},{i:1,a:-1},{b:1,i:-1},{i:1,b:-1}] as Record<string,number>[])path.set(canon(lin),{lin,holds:true})
 const tree=fieldCase(m,g,{reads:[],insts:[]},claim,path,clock()+1000)
 expect(tree).toBeDefined();if(tree)expect(check(g,tree,path)).toBe(true)
})

test('field projection does not strengthen disjunctions or discard a counted conclusion',()=>{
 const field=atMost(x('value'),n(1)),count=atMost(get('Rows',n(0)),n(2))
 expect(fieldOnlyGoal({name:'field',hyps:[any(field,count),{op:'not',x:field}]},m,cert)?.hyps).toEqual([{op:'not',x:field}])
 expect(fieldOnlyGoal({name:'count',hyps:[field,{op:'not',x:count}]},m,cert)).toBeUndefined()
})
