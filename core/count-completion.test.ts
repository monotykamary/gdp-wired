import {test,expect} from 'bun:test'
import {type Law,type E,x,get,less,same,not,any} from './machine.ts'
import {completeCountLawInstances} from './count-completion.ts'
import {assumed,check} from '../kernel/kernel.ts'
import {clock,grow} from '../kernel/prove.ts'
const n=(value:number):E=>({op:'const',value})
const law:Law={name:'rows constrain a pair',forall:'a',keys:['b'],holds:any(not(less(x('a'),x('size'))),same(get('Q',x('a')),get('Q',x('b'))))}
test('completes whole tuples of assumed laws, deduplicated, without mutating the old map',()=>{
 const at={[law.name]:[x('i'),x('i')]},before=JSON.stringify(at),r=completeCountLawInstances([law],at,[x('i'),x('j'),x('i')],()=>true)
 expect(r.added).toHaveLength(3);expect(r.at[law.name]).toHaveLength(8);expect(JSON.stringify(at)).toBe(before)
 expect(assumed([law],r.at)[1]).toEqual(any(not(less(x('i'),x('size'))),same(get('Q',x('i')),get('Q',x('j')))))
 const again=completeCountLawInstances([law],r.at,[x('i'),x('j')],()=>true);expect(again.added).toHaveLength(0);expect(again.at).toBe(r.at)
})
test('completion is bounded to four terms, binary laws, 48 new tuples and existing generation fuel',()=>{
 const wide={...law,name:'wide',keys:['b','c']},laws=[wide,...Array.from({length:5},(_,i)=>({...law,name:'pair'+i}))]
 const r=completeCountLawInstances(laws,{},Array.from({length:8},(_,i)=>n(i)),()=>true)
 expect(r.added).toHaveLength(48);expect(r.added.every(a=>a.law!=='wide'&&a.tuple.every(t=>t.op==='const'&&t.value<4))).toBe(true)
 let fuel=2;expect(completeCountLawInstances(laws,{},[n(0),n(1)],()=>true,()=>fuel-->0).added).toHaveLength(2)
 expect(completeCountLawInstances(laws,{},[n(0)],()=>false).added).toHaveLength(0)
})
test('a complete original premise, not a trusted fact, closes the ordinary checked goal',()=>{
 const source:Law={name:'count lower bound',forall:'a',holds:{op:'<=',a:n(1),b:get('Q',x('a'))}},term=x('i'),r=completeCountLawInstances([source],{},[term],()=>true)
 const goal={name:'instance replay',hyps:[...assumed([source],r.at),not({op:'<=' as const,a:n(1),b:get('Q',term)})]},out=grow(goal,new Map(),{nodes:0,until:clock()+200})
 expect('tree'in out).toBe(true);if('tree'in out)expect(check(goal,out.tree)).toBe(true)
})
