import {expect,test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {counted,fullRate,withBudget,budgetEnd,inBudget,clock,BudgetExpired,checkBudget,withDeadline,wallAt,searchNow,withWall} from '../kernel/prove.ts'
import {coreMeter} from './meter.ts'
import {traceNow} from './trace-clock.ts'
import {searchDateNow,transportEnd} from './wall.ts'

test('nested work scopes cannot extend parent and restore after an exception',()=>{
 const was=coreMeter.evals
 try{counted(fullRate,()=>withBudget(100,()=>{
  const end=budgetEnd();withBudget(10000,()=>expect(budgetEnd()).toBe(end))
  withDeadline(clock()+0.1,()=>expect(wallAt()).toBeLessThanOrEqual(clock()+0.1))
  coreMeter.evals+=1000;expect(()=>checkBudget('control')).toThrow(BudgetExpired)
 }),true)}catch(e){expect(e).toBeInstanceOf(BudgetExpired)}finally{coreMeter.evals=was}
 expect(inBudget()).toBe(false)
})

test('full profile proves and refuses unchanged rules without any clock read',()=>{
 const program=`
 import {rule,proveRule,proveSteps} from './core/dsl.ts';
 import {tripwireGate} from './core/clock-tripwire-preload.ts';
 import {strict as assert} from 'node:assert';
 import {clock,counted,fullRate,withBudget,searchNow,withWall,wallAt} from './kernel/prove.ts';
 import {traceNow} from './core/trace-clock.ts';
 import {searchDateNow,transportEnd} from './core/wall.ts';
 const r=rule('clock probe').state({v:0}).step(({v})=>({v}));
 const law=r.law('zero',({v})=>v.eq(0)),sl=r.stepLaw('same',(b,a)=>a.v.eq(b.v));
 tripwireGate.active=true;
 counted(fullRate,()=>withBudget(1000000,()=>{
   assert.equal(searchNow(),clock());assert.equal(searchDateNow(),clock());assert.equal(traceNow(),0);
   withWall(clock()+1,()=>assert(wallAt()<=clock()+1));assert(transportEnd(clock()+1)<=clock()+1);
 }),true);
 for(const search of [{work:1000000},{ms:4000},false]){
   const v=proveRule(r,[law],{search});assert(v.proven&&v.checked,JSON.stringify(v));
 }
 assert(proveSteps(r,[],[sl],{search:{work:1000000},from:'any'}).checked);
 assert(!proveRule(r.step(({v})=>({v:v.plus(1)})),[law],{search:{work:1000000}}).proven);
 assert(!proveRule(r,[law],{search:{work:0}}).proven);
 for(const work of [-1,Infinity,NaN])assert.throws(()=>proveRule(r,[law],{search:{work}}),RangeError);
 assert.throws(()=>proveRule(r,[law],{search:{work:1,ms:1}}),RangeError);
 console.log('FULL_CLOCK_PASS');`
 const env={...process.env,GDP_WORK_FULL:'1',GDP_WORK_STEPS:'0'}
 const r=spawnSync(process.execPath,['--preload','./core/clock-tripwire-preload.ts','--eval',program],{cwd:process.cwd(),env,encoding:'utf8',timeout:60000})
 expect(r.stderr).not.toContain('counted-scope wall-clock read');expect(r.status, r.stderr).toBe(0);expect(r.stdout).toContain('FULL_CLOCK_PASS')
})

test('legacy counted clock and telemetry do not read the wall',()=>{
 const p=performance.now,d=Date.now
 Object.defineProperty(performance,'now',{configurable:true,value:()=>{throw Error('wall read')}});Date.now=()=>{throw Error('date read')}
 try{counted(fullRate,()=>{expect(searchNow()).toBe(clock());expect(traceNow()).toBe(0);expect(searchDateNow()).toBe(clock())},true)}finally{Object.defineProperty(performance,'now',{configurable:true,value:p});Date.now=d}
})
