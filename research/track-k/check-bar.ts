import assert from 'node:assert/strict'
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
const dir=process.argv[2]!, report=JSON.parse(readFileSync(join(dir,'report.json'),'utf8'))
assert.equal(report.coverageErrors?.length,0,'bar coverage errors')
assert(report.results?.length,'empty bar')
for(const result of report.results){assert(!result.error,`${result.group}: ${result.error}`);assert(result.cand,`${result.group}: missing candidate`);for(const meta of result.metas??[])assert.equal(meta.code,0,`${result.group}: failed launch`)}
const views=Object.entries(report).filter(([,v]:[string,any])=>v?.candidate)
let wrong=0,solidLosses=0
for(const [,raw] of views){const view=raw as any;wrong+=Number(view.candidate.wrong??0);wrong+=(view.tasks??[]).filter((t:any)=>t.kind==='wrong').length;solidLosses+=(view.tasks??[]).filter((t:any)=>t.kind==='lost'&&t.solid).length}
assert.equal(wrong,0,'bar wrong answers');assert.equal(solidLosses,0,'bar solid losses')
const out={wrong,solidLosses,groups:report.results.map((r:any)=>r.group),wallSeconds:report.wall_s}
writeFileSync(join(dir,'verified.json'),JSON.stringify(out,null,2)+'\n');console.log(JSON.stringify(out,null,2))
