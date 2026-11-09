import {expect,test} from 'bun:test'
import {checkCohort,cpu,digest,type Cohort,type Identity} from './consensus-recheck.ts'
const identity:Identity={baseline:'1'.repeat(40),candidate:'2'.repeat(40),harness:'3'.repeat(64),counts:{base:'4'.repeat(64),candidate:'5'.repeat(64)}}
function fixture():Cohort{
 const pairs=Array.from({length:5},(_,index)=>{
  const repeat=index+1
  const side=(name:string)=>[`LANE_I_BEGIN mldr ${repeat} consensus_forall ${name}`,`LANE_I_EXIT ${name} 0`,JSON.stringify({id:'consensus_forall',search:{verdict:'proven',ms:100}}),'LANE_I_TIMING {"event":"candidates","at":20}','LANE_I_TIMING {"event":"first-attempt-return","at":30,"attemptWallMs":5}','counts: try invariant | ls 1 pass 1 ms 100 took 10 wall 5 [] -> kept','LANE_I_TIMING {"event":"result","at":110,"searchMs":100}',`LANE_I_END mldr ${repeat} consensus_forall ${name}`].join('\n')
  const log=identity.baseline+'\n'+identity.candidate+'\n'+side('base')+'\n'+side('candidate')
  return {repeat,exit:0,log,sha256:digest(log),hashes:{base:{harness:identity.harness,counts:identity.counts.base},candidate:{harness:identity.harness,counts:identity.counts.candidate}}}
 })
 return {id:1,cpu,identity,pairs}
}
test('five source-bound strict proven pairs satisfy only the prerequisite',()=>{const result=checkCohort(fixture(),identity,1);expect(result.issues).toEqual([]);expect(result.pairs).toHaveLength(5);expect(result.noLoss).toBe(true)})
test('an unknown result is retained as a loss, not a proven pair',()=>{const group=fixture(),pair=group.pairs[2]!;pair.log=pair.log.replaceAll('"proven"','"unknown"');pair.sha256=digest(pair.log);const result=checkCohort(group,identity,1);expect(result.issues).toEqual([]);expect(result.pairs[2]!.noLoss).toBe(false);expect(result.noLoss).toBe(false)})
test('duplicates, wrong source hashes and altered raw logs fail closed',()=>{
 for(const change of [(g:Cohort)=>{g.pairs[1]!.repeat=1},(g:Cohort)=>{g.pairs[1]!.hashes.base.counts='wrong'},(g:Cohort)=>{g.pairs[1]!.log+='altered'},(g:Cohort)=>{g.identity={...identity,candidate:'wrong'}},(g:Cohort)=>{g.cpu='other'}]){const group=fixture();change(group);const result=checkCohort(group,identity,1);expect(result.issues.length).toBeGreaterThan(0);expect(result.noLoss).toBe(false)}
})
test('five process exits without semantic results do not satisfy the prerequisite',()=>{const group=fixture();for(const pair of group.pairs){pair.log=pair.log.split('\n').filter(line=>!line.startsWith('{')).join('\n');pair.sha256=digest(pair.log)}const result=checkCohort(group,identity,1);expect(result.issues.length).toBeGreaterThan(0);expect(result.noLoss).toBe(false)})
