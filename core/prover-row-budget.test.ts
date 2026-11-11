import {expect,test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {type C,atMost,get,ite,min,n,not,plus,same,x} from './machine.ts'
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
test('wide row construction stops inside 1024 slack; uninterrupted reference exposes the gap',()=>{
 const code=`
 import {strict as a} from 'node:assert';
 import {atMost,get,n} from './core/machine.ts';
 import {leafConstraints} from './kernel/kernel.ts';
 import {coreMeter} from './core/meter.ts';
 import {budgetedLeafRows} from './core/prover-row-budget.ts';
 import {BudgetExpired,withBudget,fullWork} from './kernel/prove.ts';
 const goal={name:'wide',hyps:Array.from({length:256},(_,i)=>atMost(get('M',n(i)),n(1)))};
 const tableBefore=coreMeter.tableCells;const path=new Map([['x:1',{lin:{x:1},holds:true}]]);a.throws(()=>withBudget(0,()=>budgetedLeafRows({name:'path row',hyps:[]},path)),BudgetExpired);a.equal(coreMeter.tableCells-tableBefore,2);
 const start=fullWork();a.throws(()=>withBudget(128,()=>budgetedLeafRows(goal,new Map())),BudgetExpired);const stopped=fullWork()-start;a(stopped<=1152,String(stopped));
 const before=fullWork();a.throws(()=>withBudget(128,()=>leafConstraints(goal,new Map())),BudgetExpired);const uninterrupted=fullWork()-before;a(uninterrupted>1152,String(uninterrupted));
 withBudget(1e9,()=>a.deepEqual(budgetedLeafRows(goal,new Map()),leafConstraints(goal,new Map())));
 console.log('ROW_CAP_CONTROL '+JSON.stringify({stopped,uninterrupted}));`
 const run=spawnSync(process.execPath,['-e',code],{cwd:process.cwd(),env:{...process.env,GDP_WORK_FULL:'1',GDP_WORK_STEPS:'0'},encoding:'utf8',timeout:60000})
 expect(run.status,run.stdout+'\n'+run.stderr).toBe(0);expect(run.stdout).toContain('ROW_CAP_CONTROL')
})
