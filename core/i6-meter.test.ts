import {expect,test} from 'bun:test'
import {spawnSync} from 'node:child_process'

test('I6 records executed certificate/table work, cache misses and real candidate tests only in full mode',()=>{
 const code=`
 import {strict as a} from 'node:assert';
 import {checkRefutation,checkWitness} from './core/check.ts';
 import {check,canon} from './kernel/kernel.ts';
 import {rawWork} from './core/work-meter.ts';
 import {inferLaws} from './core/infer.ts';
 import {pool,poolLaw} from './examples/infer.ts';
 const enabled=process.env.GDP_WORK_FULL==='1',before=rawWork();
 a(checkRefutation([{lin:{1:1},label:''}],[{kind:'input',index:0}]));
 a.equal(rawWork().checkSteps-before.checkSteps,enabled?1:0);
 a.equal(rawWork().tableCells-before.tableCells,enabled?2:0);
 const stopped=rawWork();a.equal(checkRefutation([{lin:{1:1},label:''}],[{kind:'input',index:9},{kind:'input',index:0}]),false);
 a.equal(rawWork().checkSteps-stopped.checkSteps,enabled?1:0);
 a.equal(rawWork().tableCells-stopped.tableCells,0);
 a(checkWitness([{lin:{x:2,1:-1},label:''}],{x:0}));
 const lin={i6:2},cold=rawWork();a.equal(canon(lin),'i6:2');const warm=rawWork();a.equal(canon(lin),'i6:2');
 // f5851b032 meters itemwise key discovery/materialization; the warm lookup stays distinct.
 a.equal(warm.tableCells-cold.tableCells,enabled?9:0);a.equal(rawWork().tableCells-warm.tableCells,enabled?1:0);
 a(check({name:'constant contradiction',hyps:[{op:'<=',a:{op:'const',value:1},b:{op:'const',value:0}}]},{leaf:[{kind:'input',index:0}]}));
 const r=pool(),result=inferLaws(r,[poolLaw(r)],[],{ms:10000000});
 a(result.proven&&result.checked,JSON.stringify(result));
 const after=rawWork();
 for(const k of ['checkSteps','tableCells','cubeTests'])a.equal(after[k]>before[k],enabled,k);
 console.log('I6_SITES '+JSON.stringify({enabled,raw:Object.fromEntries(Object.keys(after).map(k=>[k,after[k]-before[k]])),proven:result.proven,checked:result.checked,found:result.found.map(f=>f.source)}));`
 for(const enabled of ['0','1']){
  const r=spawnSync(process.execPath,['--eval',code],{env:{...process.env,GDP_WORK_FULL:enabled,GDP_WORK_STEPS:'0'},encoding:'utf8',timeout:120000,maxBuffer:8*1024*1024})
  expect(r.status,r.stderr).toBe(0);expect(r.stdout).toContain('I6_SITES ')
 }
})
