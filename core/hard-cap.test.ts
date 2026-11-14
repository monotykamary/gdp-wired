import {expect,test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {rule,nat,when,min,proveRule} from './dsl.ts'

test('bounded polling protocol proves its slack and rejects the always-spend mutant',()=>{
 const r=rule('bounded polling').params({limit:nat,quantum:nat}).inputs({charge:nat}).state({spent:0})
   .step(({spent,limit,quantum,charge})=>({spent:when(spent.atMost(limit),spent.plus(min(charge,quantum)),spent)}))
 const law=r.law('slack is one bounded charge',({spent,limit,quantum})=>spent.atMost(limit.plus(quantum)))
 const yes=proveRule(r,[law],{search:false})
 expect(yes.proven).toBe(true);expect(yes.checked).toBe(true)
 const broken=r.step(({spent,quantum,charge})=>({spent:spent.plus(min(charge,quantum))}))
 expect(proveRule(broken,[law],{search:false}).proven).toBe(false)
})

test('counted binding loops and public stops preserve a 1024-unit slack',()=>{
 const code=`
 import {strict as assert} from 'node:assert';
 import {withBudget,BudgetExpired,fullWork,pastWall,late,checkWorkEndpoint,withDeadline,clock} from './kernel/prove.ts';
 import {costs} from './core/solver.ts';
 import {workLedger} from './core/work-admission.ts';
 import {interpret} from './core/machine.ts';
 import {watch} from './core/watch.ts';
 import {proveRule} from './core/dsl.ts';
 import {protocols} from './research/protocols/ic3syn/models.ts';
 const m={name:'wide bindings',params:[],inputs:[],state:{},step:{state:{}}};
 const law={name:'all bindings',forall:'i',keys:['j','k'],holds:{op:'<=',a:{op:'const',value:0},b:{op:'const',value:1}}};
 const run=interpret(m),start=fullWork();
 assert.throws(()=>withBudget(1000,()=>watch(m,run,law,{},32).start(run.init({}))),BudgetExpired);
 assert(fullWork()-start<=2024);
 // f5851b032 rejects bounded counter writes; 405b00adc makes sticky refusal explicit.
 withBudget(1,()=>assert.throws(()=>{costs.fm+=1},/unadmitted work counter mutation/));
 for(const poll of [pastWall,()=>late(Infinity)]){
  const before=fullWork();
  withBudget(1,()=>{assert.throws(()=>workLedger.start('fm',1,'hard-cap probe'),BudgetExpired);assert.doesNotThrow(poll)});
  assert.equal(fullWork(),before);
  assert.throws(()=>withBudget(1,()=>workLedger.withCapacityRefusalBoundary(()=>{
   try { workLedger.start('fm',1,'guarded hard-cap probe') } catch(error) { assert(error instanceof BudgetExpired) }
   poll();
  })),BudgetExpired);
  assert.equal(fullWork(),before);
 }
 withBudget(100000,()=>{
  assert.throws(()=>withDeadline(clock()-1,()=>assert.fail('expired scope entered')),BudgetExpired);
  assert.doesNotThrow(()=>checkWorkEndpoint('expired child does not poison parent'));
 });
 const p=protocols.find(p=>p.id==='lock_server'),r=p.make(),laws=p.laws(r);
 for(const cap of [0,64,4096,10000]){
  const before=fullWork(),v=proveRule(r,laws,{search:{work:cap}}),used=fullWork()-before;
  assert(!v.proven&&!v.checked&&v.stuck==='unknown'&&v.why.startsWith('work budget ('),JSON.stringify(v));
  assert(used<=cap+1024,JSON.stringify({cap,used}));
 }
 console.log('HARD_CAP_CONTROL_PASS');`
 const r=spawnSync(process.execPath,['--eval',code],{env:{...process.env,GDP_WORK_FULL:'1',GDP_WORK_STEPS:'0'},encoding:'utf8',timeout:60000})
 expect(r.status,r.stderr).toBe(0);expect(r.stdout).toContain('HARD_CAP_CONTROL_PASS')
})
