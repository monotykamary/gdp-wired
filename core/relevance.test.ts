import {expect,test} from 'bun:test'
import {type C,type Law,type Machine,n,x} from './machine.ts'
import {relevantGoals,relevantLaws} from './relevance.ts'
import {check,type Goal} from '../kernel/kernel.ts'
import {clock,grow,widen,withWall} from '../kernel/prove.ts'
const cell=(map:string):C=>({op:'<=',a:n(0),b:{op:'get',map,key:x('i')}})
test('relevance tiers preserve source hypotheses, order and the negative conclusion',()=>{
 const goal:Goal={name:'source',hyps:[cell('needed'),...Array.from({length:80},(_,i)=>cell('unrelated'+i)),{op:'not',x:cell('needed')}]}
 const tiers=relevantGoals(goal)
 expect(tiers.length).toBeGreaterThan(0)
 for(const part of tiers){expect(part.name).toBe(goal.name);expect(part.hyps.at(-1)).toBe(goal.hyps.at(-1));expect(part.hyps.every(h=>goal.hyps.includes(h))).toBe(true);expect(part.hyps.length).toBeLessThan(goal.hyps.length);expect(part.hyps.map(h=>goal.hyps.indexOf(h))).toEqual(part.hyps.map(h=>goal.hyps.indexOf(h)).sort((a,b)=>a-b))}
 const part=tiers[0]!,proof=withWall(performance.now()+1000,()=>grow(part,new Map(),{nodes:0,until:clock()+1000}))
 expect('tree'in proof).toBe(true)
 if('tree'in proof){const whole=widen(part,goal,proof.tree);expect(whole).toBeDefined();expect(check(goal,whole!)).toBe(true)}
})
test('law support expands count definitions and ignores coincident binder names',()=>{
 const machine:Machine={name:'count source',params:[],inputs:[],state:{},maps:{source:0},counts:{tally:{j:'j',key:'k',below:n(3),body:{op:'get',map:'source',key:x('k')}}},step:{}}
 const target:Law={name:'target',forall:'i',holds:cell('tally')}
 const support:Law={name:'source bound',forall:'i',holds:cell('source')}
 const laws=[target,...Array.from({length:40},(_,i):Law=>({name:'noise '+i,forall:'i',holds:cell('noise'+i)})),support]
 const tiers=relevantLaws(machine,laws,target)
 expect(tiers.map(t=>t.length)).toEqual([12,24])
 const medium=[target,...laws.slice(1,18),support],mediumTiers=relevantLaws(machine,medium,target)
 expect(mediumTiers.map(t=>t.length)).toEqual([12]);expect(mediumTiers[0]).toContain(target);expect(mediumTiers[0]).toContain(support)
 for(const t of tiers){expect(t).toContain(target);expect(t).toContain(support);expect(t.every(l=>laws.includes(l))).toBe(true);expect(t.map(l=>laws.indexOf(l))).toEqual(t.map(l=>laws.indexOf(l)).sort((a,b)=>a-b))}
})
test('small goals are unchanged; relevance cannot manufacture an assumption',()=>{
 expect(relevantGoals({name:'small',hyps:[cell('a')]})).toEqual([])
 const falseGoal:Goal={name:'false',hyps:[...Array.from({length:30},(_,i)=>cell('other'+i)),{op:'not',x:{op:'=',a:{op:'get',map:'target',key:n(0)},b:n(0)}}]}
 for(const part of relevantGoals(falseGoal)){const q=withWall(performance.now()+1000,()=>grow(part,new Map(),{nodes:0,until:clock()+1000}));expect('tree'in q).toBe(false)}
})
