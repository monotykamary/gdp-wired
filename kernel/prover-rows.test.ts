import {expect,test} from 'bun:test'
import {type C,atMost,get,ite,less,min,n,not,plus,same,x} from '../core/machine.ts'
import {type Goal,type Path,canon,leafConstraints} from './kernel.ts'
import {proverRows} from './prover-rows.ts'
const clone=<T>(a:T):T=>JSON.parse(JSON.stringify(a))
const row=(hyps:C[],path:Path)=>{
 const goal:Goal={name:'rows',hyps}
 expect(proverRows(goal,path)).toEqual(leafConstraints(goal,path))
 expect(proverRows({name:'another law',hyps:clone(hyps)},new Map(path))).toEqual(leafConstraints(goal,path))
}
test('shared facts retain exact rows at children, siblings and shorter prefixes',()=>{
 const a=x('a'),b=x('b'),c=x('c'),split={a:1,b:-1},key=canon(split)
 const hyps=[same(c,ite(atMost(a,b),min(a,b),plus(a,b))),not(atMost(c,n(0)))]
 for(const path of [new Map(),new Map([[key,{lin:split,holds:true}]]),new Map([[key,{lin:split,holds:false}]]),new Map()])row(hyps,path)
 expect(proverRows({name:'root',hyps},new Map()).slice(0,1)).not.toEqual(proverRows({name:'child',hyps},new Map([[key,{lin:split,holds:true}]] )).slice(1,2))
})
test('new cell equality, term bounds, natural rows and path ordering match the checker',()=>{
 const a=x('a'),b=x('b'),h=[atMost(get('M',a),get('M',b)),same(x('z'),min(a,b))],f={a:1,b:-1},g={a:-1,b:1}
 for(const holds of [true,false]){
  const entries:[string,{lin:typeof f,holds:boolean}][]=[[canon(f),{lin:f,holds}],[canon(g),{lin:g,holds}]]
  row(h,new Map(entries));row(h,new Map(entries.toReversed()))
 }
})
test('shared hypotheses are not shared fact indices, and irrelevant decisions are safe',()=>{
 const h=less(x('k'),n(3)),other=atMost(get('N',x('k')),n(9)),split={unrelated:1}
 for(const hs of [[h,other],[other,h],[clone(h),other]])for(const holds of [true,false])row(hs,new Map([[canon(split),{lin:split,holds}]]))
})
test('identical immutable goals share row arrays but reordered paths never alias',()=>{
 const a={a:1},b={b:1},h=[atMost(x('a'),x('b'))],g={name:'first',hyps:h},h2={name:'second',hyps:clone(h)}
 const p:Path=new Map([[canon(a),{lin:a,holds:true}],[canon(b),{lin:b,holds:false}]])
 expect(proverRows(g,p)).toBe(proverRows(h2,new Map(p)))
 expect(proverRows(g,p)).not.toBe(proverRows(h2,new Map([...p].toReversed())))
 row(h,new Map([...p].toReversed()))
})

test('cross-goal fact scopes retain original fact indices and path dependencies',()=>{
 const a=x('scope-a'),b=x('scope-b'),h=same(x('scope-result'),ite(atMost(a,b),min(a,b),plus(a,b))),other=less(x('scope-extra'),n(4)),split={'scope-a':1,'scope-b':-1}
 for(let i=0;i<20;i++)for(const hyps of [[h],[other,h],[h,other]]){
  const path:Path=new Map([[canon(split),{lin:split,holds:i%2===0}]])
  row(hyps,path)
 }
})

test('more than sixteen decision contexts retain exact facts when revisited',()=>{
 const xs=Array.from({length:6},(_,i)=>x(`v${i}`)),h=[same(x('r'),xs.map(a=>ite(atMost(a,n(0)),n(1),n(2))).reduce((a,b)=>plus(a,b)))]
 const paths=Array.from({length:64},(_,bits):Path=>new Map(xs.map((a,i)=>{const lin={[`v${i}`]:1};return [canon(lin),{lin,holds:!!(bits&(1<<i))}]})))
 for(const path of [...paths,...paths.toReversed()])row(h,path)
})

test('deterministic mixed conditional and tuple-key corpus matches unshared leaf rows',()=>{
 let state=12345
 const next=()=>{state=(Math.imul(state,1664525)+1013904223)>>>0;return state}
 const vars=[x('a'),x('b'),x('c')]
 for(let i=0;i<160;i++){
  const a=vars[next()%3]!,b=vars[next()%3]!,value=ite(atMost(a,b),min(a,b),plus(a,n(next()%5)))
  const h=[atMost(get('M',{op:'tup',a,b}),value),same(x('z'),value),not(less(a,n(next()%5)))]
  const path:Path=new Map()
  for(let j=0;j<3;j++){const lin={['abc'[j]!]:1,'1':-Number(next()%5)};if(next()%2)path.set(canon(lin),{lin,holds:!!(next()%2)})}
  row(h,path)
 }
})
