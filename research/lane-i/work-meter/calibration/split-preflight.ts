import {strict as assert} from 'node:assert'
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
// Observation only: phase wrappers do not meter, cap, re-order, or skip work.
export function splitPreflight(root:string){
 const files=[]
 for(const path of ['core/exists.ts','core/dsl.ts']){
  const file=join(root,path),before=readFileSync(file,'utf8');let after=before
  const replace=(a:string,b:string)=>{assert.equal(after.split(a).length,2,'unique '+a);after=after.replace(a,b)}
  if(path.endsWith('exists.ts')){
   replace('const run = interpret(m), start = run.init(p)',"const run = interpret(m), start = workPhase('small.init', () => run.init(p))")
   replace('  for (const i of m.inputs) reqs =',"  workPhase('small.requests', () => {\n  for (const i of m.inputs) reqs =")
   replace('  // (a state once: by a hash',"  })\n  // (a state once: by a hash")
   replace('  while (queue.length && all.length < cap && work > 0) {',"  workPhase('small.bfs', () => {\n  while (queue.length && all.length < cap && work > 0) {")
   replace('  if (!queue.length) return all',"  })\n  if (!queue.length) return all")
   replace('  for (let t = 0; walks > 0 && all.length < 2 * cap; t++) {',"  workPhase('small.walks', () => {\n  for (let t = 0; walks > 0 && all.length < 2 * cap; t++) {")
   replace('  return all\n}', '  })\n  return all\n}')
  }else{
   replace('  r = r.withSumsOf(laws)',"  r = workPhase('rule.with-sums', () => r.withSumsOf(laws))")
   replace('  noting(r, laws)',"  workPhase('rule.noting', () => noting(r, laws))")
   replace('  const refuted = refuteByRuns(r, laws)',"  const refuted = workPhase('rule.refute-by-runs', () => refuteByRuns(r, laws))")
  }
  if(!after.includes("from './work-ledger.ts'"))after="import {workPhase} from './work-ledger.ts'\n"+after
  writeFileSync(file,after)
  const hash=(s:string)=>createHash('sha256').update(s).digest('hex')
  files.push({path,before:hash(before),after:hash(after)})
 }
 return {kind:'observation-only phase split',files}
}
