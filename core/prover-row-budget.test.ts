import {expect,test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {type C,atMost,get,ite,less,min,n,not,plus,same,x} from './machine.ts'
import {type Goal,type Path,canon,leafConstraints} from '../kernel/kernel.ts'
import {budgetedLeafRows} from './prover-row-budget.ts'
import {withBudget} from '../kernel/prove.ts'

test('checkpointed row proposals preserve reference order through all path polarities',()=>{
 const a=x('a'),b=x('b'),split={a:1,b:-1},id=canon(split)
 const hyps:C[]=[same(x('z'),ite(atMost(a,b),min(a,b),plus(a,b))),not(atMost(get('M',{op:'tup',a,b}),n(0)))]
 for(const holds of [undefined,true,false,true]){
  const path:Path=holds===undefined?new Map():new Map([[id,{lin:split,holds}]])
  const goal:Goal={name:'checkpoint rows',hyps}
  withBudget(1e9,()=>expect(budgetedLeafRows(goal,path)).toEqual(leafConstraints(goal,path)))
 }
})
test('checkpointed shared facts retain indices and do not alias reordered hypotheses',()=>{
 const h=atMost(get('N',x('k')),n(4)),other=not(same(x('k'),n(2)))
 for(const hyps of [[h,other],[other,h],[h,other]])for(const holds of [true,false]){
  const split={k:1,'1':-3},goal:Goal={name:'reordered',hyps},path:Path=new Map([[canon(split),{lin:split,holds}]])
  withBudget(1e9,()=>expect(budgetedLeafRows(goal,path)).toEqual(leafConstraints(goal,path)))
 }
})
test('checkpointed mixed conditional and tuple-key proposals equal reference rows',()=>{
 let state=12345
 const next=()=>{state=(Math.imul(state,1664525)+1013904223)>>>0;return state}
 const vars=[x('a'),x('b'),x('c')]
 for(let i=0;i<160;i++){
  const a=vars[next()%3]!,b=vars[next()%3]!,value=ite(atMost(a,b),min(a,b),plus(a,n(next()%5)))
  const goal:Goal={name:'mixed rows',hyps:[atMost(get('M',{op:'tup',a,b}),value),same(x('z'),value),not(less(a,n(next()%5)))]}
  const path:Path=new Map()
  for(let j=0;j<3;j++){const lin={['abc'[j]!]:1,'1':-Number(next()%5)};if(next()%2)path.set(canon(lin),{lin,holds:!!(next()%2)})}
  for(const p of [path,new Map([...path].toReversed()),new Map()])withBudget(1e9,()=>expect(budgetedLeafRows(goal,p)).toEqual(leafConstraints(goal,p)))
 }
})

// 4bec30ad0 and f5851b032: both row paths admit before materialization, with no overshoot.
test('wide row construction refuses before charging and both row paths honor the exact cap',()=>{
 const code=`
 import {strict as a} from 'node:assert';
 import {atMost,get,n} from './core/machine.ts';
 import {leafConstraints} from './kernel/kernel.ts';
 import {coreMeter} from './core/meter.ts';
 import {budgetedLeafRows} from './core/prover-row-budget.ts';
 import {BudgetExpired,withBudget,fullWork} from './kernel/prove.ts';
 const goal={name:'wide',hyps:Array.from({length:256},(_,i)=>atMost(get('M',n(i)),n(1)))};
 const tableBefore=coreMeter.tableCells;const path=new Map([['x:1',{lin:{x:1},holds:true}]]);a.throws(()=>withBudget(0,()=>budgetedLeafRows({name:'path row',hyps:[]},path)),BudgetExpired);a.equal(coreMeter.tableCells-tableBefore,0);
 const start=fullWork();a.throws(()=>withBudget(128,()=>budgetedLeafRows(goal,new Map())),BudgetExpired);const stopped=fullWork()-start;a(stopped<=128,String(stopped));
 const before=fullWork();a.throws(()=>withBudget(128,()=>leafConstraints(goal,new Map())),BudgetExpired);const referenceStopped=fullWork()-before;a(referenceStopped<=128,String(referenceStopped));
 const completeStart=fullWork();withBudget(1e9,()=>a.deepEqual(budgetedLeafRows(goal,new Map()),leafConstraints(goal,new Map())));const completed=fullWork()-completeStart;a(completed>128,String(completed));
 console.log('ROW_CAP_CONTROL '+JSON.stringify({stopped,referenceStopped,completed}));`
 const run=spawnSync(process.execPath,['-e',code],{cwd:process.cwd(),env:{...process.env,GDP_WORK_FULL:'1',GDP_WORK_STEPS:'0'},encoding:'utf8',timeout:60000})
 expect(run.status,run.stdout+'\n'+run.stderr).toBe(0);expect(run.stdout).toContain('ROW_CAP_CONTROL')
})
