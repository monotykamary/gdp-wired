import {expect,test} from 'bun:test'
import {atMost,n,x} from '../core/machine.ts'
import {type Goal,type Path,canon,leafConstraints,leafConstraintsReusing} from './kernel.ts'
import {ProverRowsCache,proverRowsReusingFacts,rowReuseStorage} from './prover-rows.ts'
const row=leafConstraintsReusing({name:'row',hyps:[atMost(n(1),n(0))]},new Map())[0]!
test('facts-only rows preserve native order and do not retain leaf tables',()=>{
 const condition=atMost(x('key'),n(2)),goal:Goal={name:'facts-only',hyps:[atMost(x('value'),{op:'if',c:condition,then:n(3),else:n(5)})]},lin={key:1,'1':-2}
 const paths:Path[]=[new Map(),new Map([[canon(lin),{lin,holds:true}]]),new Map([[canon(lin),{lin,holds:false}]])]
 const before=rowReuseStorage()
 for(const path of [...paths,...paths]){
  const first=proverRowsReusingFacts(goal,path),again=proverRowsReusingFacts(goal,path),copy=proverRowsReusingFacts(structuredClone(goal),path)
  expect(first).toEqual(leafConstraints(goal,path));expect(again).toEqual(first);expect(copy).toEqual(first);expect(again).not.toBe(first)
 }
 const after=rowReuseStorage();expect(after.rowEntries).toBe(before.rowEntries);expect(after.constraints).toBe(before.constraints)
})
test('row retention counts constraint weight and keeps the most recently used entry',()=>{
 const cache=new ProverRowsCache(3),a=[row,row],b=[row],c=[row]
 cache.set('a',a);cache.set('b',b);expect(cache.weight).toBe(3)
 expect(cache.get('a')).toBe(a)
 expect(cache.set('c',c)).toBe(1)
 expect(cache.get('b')).toBeUndefined();expect(cache.get('a')).toBe(a);expect(cache.get('c')).toBe(c)
 expect(cache.weight).toBe(3)
 cache.set('a',[row]);expect(cache.weight).toBe(2)
 cache.set('large',[row,row,row,row]);expect(cache.get('large')).toBeUndefined();expect(cache.weight).toBe(2)
})
test('row retention rejects invalid budgets and supports a zero row budget',()=>{
 expect(()=>new ProverRowsCache(-1)).toThrow();expect(()=>new ProverRowsCache(NaN)).toThrow();expect(()=>new ProverRowsCache(1,0)).toThrow()
 const empty=new ProverRowsCache(0);empty.set('row',[row]);expect(empty.weight).toBe(0);expect(empty.get('row')).toBeUndefined()
})

test('row retention also bounds zero-weight entries without changing returned arrays',()=>{
 const cache=new ProverRowsCache(3,2),a:typeof row[]=[],b:typeof row[]=[],c:typeof row[]=[]
 cache.set('a',a);cache.set('b',b);cache.set('c',c)
 expect(cache.size).toBe(2);expect(cache.weight).toBe(0);expect(cache.get('a')).toBeUndefined();expect(cache.get('b')).toBe(b);expect(cache.get('c')).toBe(c)
})
