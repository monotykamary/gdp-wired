import {expect,test} from 'bun:test'
import {type Law,type Machine,n,x} from './machine.ts'
import {admitCountedFamily} from './counts.ts'
import {checkCountedLaws} from '../kernel/kernel.ts'
import {clock,counted,fullRate,withDeadline,withWall} from '../kernel/prove.ts'

const fixture=(right:number)=>{
 const m:Machine={name:'dependency closure',params:[],inputs:[],state:{left:n(0),right:n(0)},step:{state:{left:x('right'),right:n(right)}}}
 const caller:Law={name:'left stays zero',holds:{op:'=',a:x('left'),b:n(0)}},helper:Law={name:'right stays zero',holds:{op:'=',a:x('right'),b:n(0)}},noise:Law={name:'unneeded false guess',holds:{op:'=',a:x('left'),b:n(1)}}
 return {m,caller,helper,noise,all:[caller,helper,noise]}
}
const run=(f:ReturnType<typeof fixture>,support=true)=>withWall(performance.now()+5000,()=>counted(fullRate,()=>{const until=clock()+2000;return withDeadline(until,()=>admitCountedFamily(f.m,[f.caller],f.all,new Set(support?[f.helper]:[]),until))},true))

test('dependency admission closes the needed helpers and excludes unneeded false guesses',()=>{
 const f=fixture(0),out=run(f)
 expect(out.proven).toBe(true);expect(out.laws).toContain(f.caller);expect(out.laws).toContain(f.helper);expect(out.laws).not.toContain(f.noise)
 expect(out.proof).toBeDefined();if(out.proof)expect(checkCountedLaws(out.m,out.laws,out.proof)).toBe(true)
})
test('a needed but noninductive helper cannot authorize the caller',()=>{
 const out=run(fixture(1));expect(out.proven).toBe(false)
})
test('the no-support path still returns a checked family',()=>{
 const out=run(fixture(0),false);expect(out.proven).toBe(true);if(out.proof)expect(checkCountedLaws(out.m,out.laws,out.proof)).toBe(true)
})
test('missing callers and exhausted admission budgets cannot produce success',()=>{
 const f=fixture(0)
 expect(admitCountedFamily(f.m,[f.caller],[f.helper],new Set([f.helper]),clock()).proven).toBe(false)
 const out=withWall(performance.now()+1000,()=>counted(fullRate,()=>admitCountedFamily(f.m,[f.caller],f.all,new Set([f.helper]),clock()),true))
 expect(out.proven).toBe(false);expect(out.laws).toContain(f.caller)
})
