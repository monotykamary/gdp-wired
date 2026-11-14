import {expect, test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {rule,nat,when,proveRule} from './dsl.ts'

test('pre-admission policy is checked and the always-spend mutation is rejected',()=>{
 const r=rule('native pre-admission').params({limit:nat}).inputs({charge:nat}).state({spent:0})
   .step(({spent,charge,limit})=>({spent:when(spent.plus(charge).atMost(limit),spent.plus(charge),spent)}))
 const law=r.law('never overdraw',({spent,limit})=>spent.atMost(limit))
 const yes=proveRule(r,[law],{search:false})
 expect(yes.proven).toBe(true);expect(yes.checked).toBe(true)
 const broken=r.step(({spent,charge})=>({spent:spent.plus(charge)}))
 expect(proveRule(broken,[law],{search:false}).proven).toBe(false)
})

const program = `
import {strict as a} from 'node:assert';
import {withBudget,BudgetExpired,fullWork,checkWorkEndpoint} from './kernel/prove.ts';
import {rawWork,workKeys,weightedWork} from './core/work-meter.ts';
import {completeWorkProfile as profile} from './core/work-profile.ts';
import {workLedger} from './core/work-admission.ts';
import {workAdd,workMultiply,workAmount,workToNumber,zeroWork} from './core/work-amount.ts';
import {tinyNode,tinyTerm,tinyBlock,reachState,reachEdge,observeEval,withReachabilityWork} from './core/work-observe.ts';
import {compileC,fastStep} from './core/machine.ts';
import {tinyFiniteCandidates} from './core/finite-tiny.ts';
import {tripwireGate} from './core/clock-tripwire-preload.ts';
a.equal(profile.id,'raw-work-v1');a.equal(workKeys.length,26);tripwireGate.active=true;
const before=rawWork();
if(profile.enabled){
 for(const action of [tinyNode,tinyTerm,reachState,reachEdge,()=>withReachabilityWork(()=>observeEval()),()=>withReachabilityWork(()=>observeEval(7,true))]){
  const old=rawWork(),used=fullWork();a.throws(()=>withBudget(0,action),BudgetExpired);a.deepEqual(rawWork(),old);a.equal(fullWork(),used);
 }
 // f5851b032: refusal is atomic; 405b00adc makes sticky cancellation opt-in.
 const refused=rawWork(),used=fullWork();
 withBudget(1,()=>{a.throws(()=>withReachabilityWork(()=>observeEval(100,true)),BudgetExpired);checkWorkEndpoint('unprotected refusal')});
 a.deepEqual(rawWork(),refused);a.equal(fullWork(),used);
 a.throws(()=>withBudget(1,()=>workLedger.withCapacityRefusalBoundary(()=>{try{withReachabilityWork(()=>observeEval(100,true))}catch{}checkWorkEndpoint('protected refusal')})),BudgetExpired);
 a.deepEqual(rawWork(),refused);a.equal(fullWork(),used);
 withBudget(100,()=>{a.throws(()=>withBudget(0,tinyTerm),BudgetExpired);tinyTerm()});
 withBudget(0,()=>{try{withBudget(10,tinyTerm)}catch{}checkWorkEndpoint('unprotected shared end')});
 a.throws(()=>withBudget(1,()=>{try{withReachabilityWork(()=>observeEval(100,true))}catch{}a.throws(()=>withBudget(0.1,tinyTerm),BudgetExpired);tinyBlock(1,tinyTerm);tinyTerm()}),BudgetExpired);
 const start=rawWork().tinyTerms;
 a.throws(()=>withBudget(2,()=>tinyBlock(100,()=>{tinyTerm();tinyTerm();tinyTerm()})),BudgetExpired);
 a.equal(rawWork().tinyTerms-start,2);
 withBudget(100,()=>tinyBlock(40,()=>{tinyTerm();tinyBlock(30,()=>tinyTerm())}));
 a.equal(rawWork().tinyTerms-start,4);
 a.throws(()=>withBudget(100,()=>tinyBlock(40,()=>{tinyTerm();throw Error('restore')})),/restore/);
 a.throws(()=>withBudget(0,tinyTerm),BudgetExpired);
}
const m={name:'native tiny',params:[],inputs:['op'],state:{x:{op:'const',value:0}},maps:{},counts:{C:{key:'i',below:{op:'const',value:1},body:{op:'const',value:0}}},step:{state:{x:{op:'var',name:'op'}}}};
const law={name:'zero',holds:{op:'=',a:{op:'var',name:'x'},b:{op:'const',value:0}}};
const node0=rawWork().tinyNodes,term0=rawWork().tinyTerms,candidates=[];
const stats=withBudget(10000000,()=>tinyFiniteCandidates(m,m,[law],{},(pre,request,laws)=>{candidates.push([pre.scalars,request,laws.map(l=>l.name)]);return true},{valueDomain:[0,1],postTargetPruning:true,postTargetIntervals:true}));
a(stats.completed,JSON.stringify(stats));a(stats.nodes>0,JSON.stringify(stats));
if(profile.enabled){a.equal(rawWork().tinyNodes-node0,stats.nodes);a(rawWork().tinyTerms>term0)}
const test=compileC(law.holds,m),st={scalars:{x:0},maps:{}};
withBudget(10000000,()=>withReachabilityWork(()=>{reachState();test({},st);withReachabilityWork(()=>test({},st));const step=fastStep(m);a(step);reachEdge();step({},st,{op:1})}));
const last=rawWork();for(const k of workKeys)a(Number.isSafeInteger(last[k])&&last[k]>=before[k],k);
if(profile.enabled){
 const exact=workKeys.reduce((sum,key)=>workAdd(sum,workMultiply(workLedger.weights[key],workAmount(BigInt(last[key])))),zeroWork);
 a.deepEqual(exact,workLedger.actual());a.equal(workToNumber(exact),fullWork());
}else a.equal(weightedWork(last),fullWork());
if(profile.enabled){for(const k of ['tinyNodes','tinyTerms','reachStates','reachEdges','reachEvals','reachCompiledEvals'])a(last[k]>before[k],k)}
else for(const k of ['tinyNodes','tinyTerms','reachStates','reachEdges','reachEvals','reachCompiledEvals'])a.equal(last[k],0,k);
tripwireGate.active=false;console.log('NATIVE_RESULT '+JSON.stringify({candidates,stats:{...stats,ms:0},coverage:Object.fromEntries(workKeys.map(k=>[k,last[k]-before[k]]))}));`
function child(full: boolean) {
 const r=spawnSync(process.execPath,['--preload','./core/clock-tripwire-preload.ts','--eval',program],{env:{...process.env,GDP_WORK_FULL:full?'1':'0',GDP_WORK_STEPS:'0'},encoding:'utf8',timeout:60000})
 expect(r.status,r.stderr).toBe(0)
 const line=r.stdout.split('\n').find(s=>s.startsWith('NATIVE_RESULT '))
 expect(line,r.stdout).toBeDefined()
 return JSON.parse(line!.slice(14))
}
test('successor raw counters admit before work, meter native pruning, and restore nested scopes',()=>{child(true)})
test('finite result stays exact with flags off and all successor fields zero',()=>{
 const a=child(true),b=child(false)
 expect(a.candidates).toEqual(b.candidates);expect(a.stats).toEqual(b.stats)
})
