import {expect,test} from 'bun:test'
import {atMost,n} from '../core/machine.ts'
import {leafConstraintsReusing} from './kernel.ts'
import {ProverRowsCache} from './prover-rows.ts'
const row=leafConstraintsReusing({name:'row',hyps:[atMost(n(1),n(0))]},new Map())[0]!
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
