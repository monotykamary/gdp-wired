import {expect,test} from 'bun:test'
import {type Machine,all,any,atMost,get,ite,less,minus,n,not,plus,same,times,x} from '../machine.ts'
import {type CountCert,type Path,canon,check,linear,mcGoal} from '../../kernel/kernel.ts'
import {clock,grow,widen} from '../../kernel/prove.ts'
import {fieldOnlyGoal} from './field-only.ts'
import {fieldCase,fieldDirection} from './field-case.ts'
import {sourceProofMemo} from './source-memo.ts'
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

test('shifted copy fields prove both natural-subtraction directions',()=>{
 const m:Machine={name:'shifted copy',params:['size'],inputs:['i','j'],state:{},maps:{Config:0},step:{}},a=x('a'),b=x('b'),i=x('i'),j=x('j'),c=x('c'),size=x('size'),index=(r:typeof a)=>plus(times(64,r),c)
 const cell=(r:typeof a)=>{const key=index(r),inside=all(atMost(times(64,j),key),less(key,plus(times(64,j),n(64)))),forward=atMost(j,i);return ite(any(all(inside,any(all(forward,same(get('Config',plus(key,times(64,minus(i,j)))),n(1))),all(not(forward),same(get('Config',minus(key,times(64,minus(j,i)))),n(1))))),all(not(inside),same(get('Config',key),n(1)))),n(1),n(0))}
 const claim=not(any(not(all(less(a,size),less(b,size),less(c,size))),same(cell(a),cell(b)))),g={name:'shifted',hyps:[all(atMost(n(1),size),atMost(size,n(64))),claim]},path:Path=new Map(),events:Record<string,unknown>[]=[]
 for(const lin of [{a:1,j:-1},{j:1,a:-1},{b:1,j:-1},{j:1,b:-1}] as Record<string,number>[])path.set(canon(lin),{lin,holds:true})
 const tree=fieldCase(m,g,{reads:[],insts:[]},claim,path,clock()+1500,event=>events.push(event))
 expect(tree).toBeDefined();if(tree)expect(check(g,tree,path)).toBe(true)
 expect(events.some(event=>event.stage==='field-natural-direction'&&event.proposed)).toBe(true)
 // A forced cell comparison still needs the choices inside its read key.
 const forced=atMost(n(1),cell(a)),value=linear(cell(a),path)!,lin=Object.fromEntries(Object.entries(value).map(([key,n])=>[key,-n]))
 lin['1']=(lin['1']??0)+1
 const forcedPath=new Map(path).set(canon(lin),{lin,holds:true})
 expect(fieldDirection(forced,forcedPath)).toBeDefined()
})

test('field arithmetic leaves close before the model query and remain checked',()=>{
 const cell=get('Value',x('row')),claim=less(n(3),cell),g={name:'linear field',hyps:[atMost(cell,n(3)),claim]},events:Record<string,unknown>[]=[]
 const tree=fieldCase(m,g,cert,claim,new Map(),clock()+1000,event=>events.push(event))
 expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)
 expect(events.some(event=>event.stage==='field-case'&&event.outcome==='linear'&&event.proposed)).toBe(true)
})
test('field memo transports completed subproofs but refuses missing source support',()=>{
 const cell=get('Value',x('row')),bound=atMost(cell,n(3)),claim=less(n(3),cell),g={name:'source field',hyps:[bound,claim]},memo=sourceProofMemo(),events:Record<string,unknown>[]=[]
 const first=fieldCase(m,g,cert,claim,new Map(),clock()+1000,undefined,0,memo)
 expect(first).toBeDefined()
 const other={name:'destination field',hyps:[atMost(x('extra'),n(0)),bound,claim]},got=fieldCase(m,other,cert,claim,new Map(),clock()+1000,event=>events.push(event),0,memo)
 expect(got).toBeDefined();if(got)expect(check(other,got)).toBe(true)
 expect(events.some(event=>event.stage==='source-memo'&&event.scope==='field-case')).toBe(true)
 expect(fieldCase(m,{name:'missing bound',hyps:[claim]},cert,claim,new Map(),clock()+300,undefined,0,memo)).toBeUndefined()
})
test('field arithmetic shortcut cannot close a satisfiable source',()=>{
 const cell=get('Value',x('row')),claim=less(n(3),cell),g={name:'possible field',hyps:[atMost(n(0),cell),claim]}
 expect(fieldCase(m,g,cert,claim,new Map(),clock()+300)).toBeUndefined()
})

test('field projection does not strengthen disjunctions or discard a counted conclusion',()=>{
 const field=atMost(x('value'),n(1)),count=atMost(get('Rows',n(0)),n(2))
 expect(fieldOnlyGoal({name:'field',hyps:[any(field,count),{op:'not',x:field}]},m,cert)?.hyps).toEqual([{op:'not',x:field}])
 expect(fieldOnlyGoal({name:'count',hyps:[field,{op:'not',x:count}]},m,cert)).toBeUndefined()
})
