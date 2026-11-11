import {expect,test} from 'bun:test'
import {countPrerequisiteComponents} from './count-prerequisite-components.ts'
import {countComponentAttemptBudget} from './count-component-budget.ts'
import {reserveCheckedCountClosing,reserveCountClosing,type CountClosingBudget} from './count-closing-budget.ts'
import {countTierBudget} from './count-tier-budget.ts'

test('checked scheduling rediscovers a parked law only after committed progress',()=>{
 const q=countPrerequisiteComponents(['early','late','core'],new Map(),['core'],[],{discoveryFirst:true,proofGuided:true,targets:['core']})
 expect(q.next()).toMatchObject({name:'early',purpose:'discovery',context:['early']})
 q.finish('early',{kind:'unknown',reason:'narrow-sat'})
 expect(q.next()).toMatchObject({name:'late',purpose:'discovery'})
 q.finish('late',[]);q.commit(['late'])
 expect(q.next()).toMatchObject({name:'early',purpose:'discovery',context:['early','late']})
 q.finish('early',['late']);q.commit(['early'])
 expect(q.next()).toMatchObject({name:'core',purpose:'required'})
 q.finish('core',[]);q.commit(['core'])
 expect(q.next()).toBeUndefined();expect(q.available()).toEqual(['early','late','core'])
})
test('a discovery fixed point without progress terminates and retains its stamp',()=>{
 const q=countPrerequisiteComponents(['extra','core'],new Map(),['core'],[],{discoveryFirst:true,proofGuided:true,targets:['core']})
 q.next();q.finish('extra',{kind:'unknown',reason:'narrow-sat'})
 q.next();q.finish('core',{kind:'unknown',reason:'budget-expired'})
 expect(q.next()).toBeUndefined();expect(q.next()).toBeUndefined()
 const next=countPrerequisiteComponents(['extra','core'],new Map(),['core'],[],{discoveryFirst:true,proofGuided:true,targets:['core'],discovered:q.discovered(),discoveryContexts:q.discoveryContexts()})
 expect(next.next()).toMatchObject({name:'core',purpose:'required'})
})
test('known strategies precede ordinary work and every ordinary first pass precedes a retry',()=>{
 const q=countPrerequisiteComponents(['a','b','strategy'],new Map([['strategy',['a','b']]]),['strategy'],[],{discoveryFirst:true,proofGuided:true,targets:['strategy'],costs:new Map([['a',0],['b',1],['strategy',100]])})
 q.next();q.finish('a',{kind:'unknown',reason:'narrow-sat'})
 q.next();q.finish('b',{kind:'unknown',reason:'narrow-sat'})
 expect(q.next()).toMatchObject({name:'strategy',purpose:'required',pass:0})
 q.finish('strategy',['a','b'])
 expect(q.next()).toMatchObject({name:'a',pass:0});q.finish('a',{kind:'unknown',reason:'sat'})
 expect(q.next()).toMatchObject({name:'b',pass:0});q.finish('b',{kind:'unknown',reason:'sat'})
 expect(q.next()).toMatchObject({name:'a',pass:1});q.finish('a',{kind:'unknown',reason:'budget-expired'})
 expect(q.next()).toMatchObject({name:'b',pass:1});q.finish('b',{kind:'unknown',reason:'budget-expired'})
 expect(q.next()).toBeUndefined();expect(q.available()).toEqual([])
})
test('component growth does not put a retry ahead of an unrun required member',()=>{
 const q=countPrerequisiteComponents(['a','b','first','later'],new Map([['first',['a']],['later',['first']]]),['first','later'],[],{discoveryFirst:true,proofGuided:true,targets:['later'],costs:new Map([['a',0],['b',1],['first',10],['later',100]])})
 q.next();q.finish('a',{kind:'unknown',reason:'narrow-sat'})
 q.next();q.finish('b',{kind:'unknown',reason:'narrow-sat'})
 expect(q.next()).toMatchObject({name:'first'});q.finish('first',['a'])
 // The other unrun known strategy takes priority across components.
 expect(q.next()).toMatchObject({name:'later'});q.finish('later',['a','b','first'])
 expect(q.next()).toMatchObject({name:'a',pass:0});q.finish('a',{kind:'unknown',reason:'sat'})
 expect(q.next()).toMatchObject({name:'b',pass:0});q.finish('b',{kind:'unknown',reason:'sat'})
 expect(q.next()).toMatchObject({name:'a',pass:1})
})

test('fair shares preserve the common endpoint and unused shares return to the pool',()=>{
 for(const width of [0,0.1,1,10,1e6])for(const pending of [1,2,3,49]){
  const part=countComponentAttemptBudget(7,7+width,pending,1,true)
  expect(part.allotted).toBeCloseTo(width/pending,8)
  expect(part.allotted+part.reserved).toBeCloseTo(width,8)
  expect(part.end).toBeLessThanOrEqual(7+width)
 }
 expect(countComponentAttemptBudget(0,90,3,1,true).allotted).toBe(30)
 expect(countComponentAttemptBudget(10,90,2,1,true).allotted).toBe(40)
 // Broken control: the old minimum-only policy gives almost all work away.
 expect(countComponentAttemptBudget(0,90,3).allotted).toBe(88)
})
test('checked packet reserve is measured, clamped to unspent root, and not a new grant',()=>{
 const base=reserveCountClosing(countTierBudget(100,1000100,3),true) as CountClosingBudget
 expect(reserveCheckedCountClosing(base,[],100)).toBe(base)
 const small=reserveCheckedCountClosing(base,[10,20],200)
 expect(small.closingFloor).toBe(60);expect(small.until).toBe(base.until)
 expect(small.searchUntil+small.closingFloor).toBe(base.until)
 expect(small.generationUntil).toBe(base.generationUntil)
 const large=reserveCheckedCountClosing(small,[1e6],900100)
 expect(large.closingFloor).toBe(100000);expect(large.searchUntil).toBe(900100)
 expect(large.strategyUntil).toBe(900100);expect(large.ordinaryFloor).toBe(0)
 expect(()=>reserveCheckedCountClosing(base,[NaN],100)).toThrow(RangeError)
 expect(()=>reserveCheckedCountClosing(base,[-1],100)).toThrow(RangeError)
 expect(()=>reserveCheckedCountClosing(base,[1],Infinity)).toThrow(RangeError)
})
