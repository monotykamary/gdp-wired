import {test,expect} from 'bun:test'
import {countedObligations,mcGoal} from '../../kernel/kernel.ts'
import {safetyContext} from './historical/safety-context.ts'
import {directSafety,originalFocusInstances} from './historical/safety-direct-context.ts'
test('direct decision package preserves all original instances, count choices, and rows',()=>{
  const c=safetyContext(),focus=originalFocusInstances(c),d=directSafety(c,focus)
  for(const [key,terms]of Object.entries(focus))expect(d.instances[key]!.slice(0,terms.length)).toEqual(terms)
  expect(d.reads.slice(0,c.metadata.reads.length)).toEqual(c.metadata.reads)
  expect(d.insts.slice(0,c.metadata.insts.length)).toEqual(c.metadata.insts)
  expect(d.picks).toEqual(c.metadata.picks)
  expect(d.addedLawTuples).toBeLessThanOrEqual(8);expect(d.addedCountInstances).toBe(6);expect(d.reads.length).toBe(17)
  const base=countedObligations(c.input.m,c.input.laws,{[c.input.law.name]:d.instances},c.input.laws.findIndex(l=>l.name===c.input.law.name)).find(x=>x.goal.name.endsWith('@step'))!
  const goal=mcGoal(base.goal.hyps,base.decls,d)!,available=new Map<string,number>()
  for(const row of goal.hyps){const k=JSON.stringify(row);available.set(k,(available.get(k)??0)+1)}
  for(const row of c.original.hyps){const k=JSON.stringify(row),n=available.get(k)??0;if(!n)throw Error('old row absent');available.set(k,n-1)}
  expect(goal.hyps.length).toBeGreaterThan(226)
})
