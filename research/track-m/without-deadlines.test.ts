import {test,expect} from 'bun:test'
import {withoutDeadlines,realNow} from './without-deadlines.ts'
import {clock,counted,fullRate,fullWork,late,pastWall,withDeadline,withWall,grow} from '../../kernel/prove.ts'
import {check} from '../../kernel/kernel.ts'
import {n,x} from '../../core/machine.ts'
test('unlimited research clock disables positive deadlines but preserves measured work and checking',()=>{
 const g={name:'research clock control',hyps:[{op:'<' as const,a:x('n'),b:n(0)}]},before=fullWork(),start=realNow(),old=Reflect.get(performance,'now')
 const bounded=withWall(1,()=>grow(g,new Map(),{nodes:0,until:1e-12}))
 expect('tree'in bounded).toBe(false)
 const tree=withoutDeadlines(()=>withWall(1,()=>withDeadline(1e-12,()=>{
  expect(clock()).toBe(0);expect(performance.now()).toBe(0)
  const out=grow(g,new Map(),{nodes:0,until:1e-12})
  expect(late(1e-12)).toBe(false);expect(pastWall()).toBe(false)
  return 'tree'in out?out.tree:undefined
 })))
 expect(fullWork()).toBeGreaterThan(before);expect(realNow()).toBeGreaterThanOrEqual(start)
 expect(Reflect.get(performance,'now')).toBe(old);expect(performance.now()).toBeGreaterThan(0)
 expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)
})
test('the research override restores clocks on exceptions',()=>{
 const old=Reflect.get(performance,'now')
 expect(()=>withoutDeadlines(()=>{throw new Error('probe')})).toThrow('probe')
 expect(Reflect.get(performance,'now')).toBe(old);expect(clock()).toBeGreaterThan(0)
})
test('a used bounded counted scope cannot silently masquerade as unlimited',()=>{
 const old=Reflect.get(performance,'now')
 counted(fullRate,()=>expect(()=>withoutDeadlines(()=>undefined)).toThrow('outside another counted scope'),true)
 expect(Reflect.get(performance,'now')).toBe(old)
})
