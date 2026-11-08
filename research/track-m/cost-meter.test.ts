import {expect,test} from 'bun:test'
import {CostMeter} from './cost-meter.ts'
test('exclusive cost phases sum to elapsed wall without double counting',()=>{
 let now=0;const p=new CostMeter(true,()=>now)
 expect(p.run('construction','root',()=>{now=2;p.run('search','search',()=>{now=3;p.run('construction','rows',()=>{now=5});now=7});now=10;return 17})).toBe(17)
 const s=p.snapshot().phases
 expect(s.construction?.exclusiveMs).toBe(7);expect(s.search?.exclusiveMs).toBe(3)
 expect(Object.values(s).reduce((n,x)=>n+x.exclusiveMs,0)).toBe(10)
})
test('kernel check owns nested row work and generation owns its internal probes',()=>{
 let now=0;const p=new CostMeter(true,()=>now)
 p.run('generation','candidates',()=>{now=1;p.run('search','probe',()=>{now=2;p.run('kernel','check',()=>{now=3;p.run('construction','rows',()=>{now=5})});now=6});now=7},true)
 const s=p.snapshot().phases
 expect(s.generation?.exclusiveMs).toBe(4);expect(s.kernel?.exclusiveMs).toBe(3)
 expect(s.search).toBeUndefined();expect(s.construction).toBeUndefined()
})
test('unfold owns arithmetic reconstruction; exceptions restore the stack',()=>{
 let now=0;const p=new CostMeter(true,()=>now)
 expect(()=>p.run('construction','unfold',()=>{now=1;p.run('search','rebuild leaf',()=>{now=3});throw new Error('sentinel')},true)).toThrow('sentinel')
 p.run('search','next',()=>{now=5})
 expect(p.snapshot().phases.construction?.exclusiveMs).toBe(3)
 expect(p.snapshot().phases.search?.exclusiveMs).toBe(2)
})
test('disabled meter does not read the clock or change an outcome',()=>{
 const p=new CostMeter(false,()=>{throw new Error('clock')})
 expect(p.run('kernel','disabled',()=>false)).toBe(false);expect(p.snapshot()).toEqual({phases:{},sites:{}})
})
