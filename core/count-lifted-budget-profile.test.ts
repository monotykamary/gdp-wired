import {expect,it} from 'bun:test'
import {spawnSync} from 'node:child_process'
for(const full of ['0','1'])it('clips original W once with FULL='+full,()=>{
 const code=`import {liftedWorkBudget,liftedCaseUntil,liftedLeafUntil} from './core/count-lifted-budget.ts';import {clock,withBudget} from './kernel/prove.ts';withBudget(250000000,()=>{const start=clock(),parent=start+1000000,b=liftedWorkBudget(4000000),options={leafUnits:b.leafUnits},caseEnd=liftedCaseUntil(parent,b),leafEnd=liftedLeafUntil(caseEnd,options),frameEnd=liftedCaseUntil(parent,b,true);console.log(JSON.stringify({full:b.full,caseDelta:caseEnd-start,leafDelta:leafEnd-start,frameDelta:frameEnd-start,clamp:liftedLeafUntil(start+1,options)-start,nested:liftedLeafUntil(start+7,options)-start,expired:liftedLeafUntil(start-1,options)-start,defaultLeafDelta:liftedLeafUntil(parent,{})-start}));});`
 const p=spawnSync(process.execPath,['-e',code],{cwd:process.cwd(),env:{...process.env,GDP_WORK_FULL:full,GDP_WORK_STEPS:'0'},encoding:'utf8'})
 expect(p.status).toBe(0);if(p.status!==0)throw Error(p.stderr)
 const r=JSON.parse(p.stdout.trim()),enabled=full==='1'
 expect(r.full).toBe(enabled);expect(r.caseDelta).toBe(enabled?4000000/30:2000);expect(r.leafDelta).toBe(enabled?4000000/120:500);expect(r.frameDelta).toBe(enabled?4000000/30:500)
 expect(r.clamp).toBe(1);expect(r.nested).toBe(7);expect(r.expired).toBe(-1);expect(r.defaultLeafDelta).toBe(500)
})
