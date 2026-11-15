import {expect,test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {completeWorkKeys} from './work-profile.ts'

// f5851b032: FULL telemetry rounds an exact sum once; flags-off retains ordered floating addition.
test('aggregation matches its exact FULL or ordered legacy reference for every column and mixed vector',()=>{
 const code=`
 import {strict as a} from 'node:assert';
 import {costs} from './core/solver.ts';
 import {coreMeter} from './core/meter.ts';
 import {eprMeter} from './kernel/epr.ts';
 import {rawWork,workKeys,fullWork,weightedWork,legacyWeights,extraWorkKeys} from './core/work-meter.ts';
 import {completeWorkProfile} from './core/work-profile.ts';
 import {workAdd,workMultiply,workFromNumber,workAmount,workToNumber,zeroWork} from './core/work-amount.ts';
 const old=rawWork();let seed=1701;
 const set=(k,n)=>{if(k==='epr')eprMeter.n=n;else if(k in coreMeter)coreMeter[k]=n;else costs[k]=n};
 const weights=Object.fromEntries([...legacyWeights,...extraWorkKeys.map(key=>[key,completeWorkProfile.weights[key]])]);
 const exact=raw=>workToNumber(workKeys.reduce((sum,key)=>workAdd(sum,workMultiply(workFromNumber(weights[key]),workAmount(BigInt(raw[key])))),zeroWork));
 const check=()=>{const raw=rawWork(),expected=completeWorkProfile.enabled?exact(raw):weightedWork(raw);a(Object.is(fullWork(),expected),JSON.stringify({actual:fullWork(),expected}))};
 try{
  for(const k of workKeys)set(k,0);
  for(const k of workKeys){for(const n of [1,7,2147483649,1099511627775]){set(k,n);check()}set(k,0)}
  for(let i=0;i<1000;i++){for(const k of workKeys){seed=(Math.imul(seed,1664525)+1013904223)>>>0;set(k,seed*257)}check()}
 }finally{for(const k of workKeys)set(k,old[k])}
 console.log('ORDERED_SUM_IDENTICAL');`
 for(const enabled of ['0','1'])for(const weight of [0.02,0.17,3.125]){
  const env={...process.env,GDP_WORK_FULL:enabled,GDP_WORK_STEPS:'0',GDP_WORK_WEIGHTS:JSON.stringify(Object.fromEntries(completeWorkKeys.map(k=>[k,weight])))}
  const r=spawnSync(process.execPath,['--eval',code],{env,encoding:'utf8',timeout:60000})
  expect(r.status,r.stderr).toBe(0);expect(r.stdout).toContain('ORDERED_SUM_IDENTICAL')
 }
})
