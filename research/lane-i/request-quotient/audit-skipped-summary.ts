import {strict as a} from 'node:assert'
import {readFileSync,readdirSync} from 'node:fs'
import {join} from 'node:path'
const [dir,source,samplerHash,oldDir]=process.argv.slice(2)
const files=readdirSync(dir!).filter(f=>f.startsWith('quotient-audit-skips-')&&f.endsWith('.log')).sort();a.equal(files.length,29)
function receipt(path:string){const lines=readFileSync(path,'utf8').split('\n').filter(l=>l.startsWith('QUOTIENT_SKIPPED_AUDIT '));a.equal(lines.length,1,path);return JSON.parse(lines[0]!.slice('QUOTIENT_SKIPPED_AUDIT '.length))}
function histogram(rows:any[],expected:number){
 a.equal(rows.reduce((n,r)=>n+r.count,0),expected)
 for(const r of rows){
  a.equal(r.kind,'guard-refusal');a.equal(r.exceptionClass,'RangeError');a(Number.isSafeInteger(r.count)&&r.count>0)
  a(r.message.endsWith(": the request fails the rule's assumption, so no proof covers the step it would take"))
  a.equal(r.origin.file,'core/machine.ts');a.equal(r.origin.sha256,'03d69e7e9e768a7e6735294f819da90d965f73d72c4134ab9ef74715d36f51bf');a.equal(r.origin.line,819)
  a.equal(r.origin.expression,'if (m.assume && !evalC(m.assume, env, st, plain)) throw new RangeError(refused(m))');a(/^[a-f0-9]{64}$/.test(r.origin.guardSHA256))
 }
}
const sameRow=(r:any)=>({params:r.params,states:r.states,digest:r.digest,skipped:r.skipped,matched:r.matched,refused:r.refused,kept:r.kept})
const rows=files.map(file=>{
 const r=receipt(join(dir!,file)),old=receipt(join(oldDir!,file))
 a.equal(r.id,file.slice('quotient-audit-skips-'.length,-4));a.equal(r.source,source);a.equal(r.originalSamplerSHA256,samplerHash);a.equal(r.adapterEdits,2)
 a.equal(r.originalInterpreterSHA256,'03d69e7e9e768a7e6735294f819da90d965f73d72c4134ab9ef74715d36f51bf');a.equal(r.interpreterAdapterEdits,1)
 a.equal(r.unexpected,0);a.equal(r.skipped,r.matched+r.refused)
 a.deepEqual(r.refusalKinds,{guard:r.refused,precondition:0,declaredFailure:0,unexpected:0});histogram(r.exceptionHistogram,r.refused)
 for(const p of r.rows){a.equal(p.unexpected,0);histogram(p.exceptionHistogram,p.refused)}
 for(const key of ['skipped','matched','refused','kept']){a.equal(r.rows.reduce((n:number,p:any)=>n+p[key],0),r[key]);a.equal(r[key],old[key])}
 a.deepEqual(r.rows.map(sameRow),old.rows.map(sameRow))
 return{id:r.id,skipped:r.skipped,matched:r.matched,refused:r.refused,unexpected:r.unexpected,kept:r.kept,exceptionHistogram:r.exceptionHistogram,rows:r.rows}
})
a(rows.some(r=>r.id==='mldr'&&r.skipped>0))
const sum=(key:'skipped'|'matched'|'refused'|'unexpected')=>rows.reduce((n,r)=>n+r[key],0)
console.log('QUOTIENT_SKIPPED_SUMMARY '+JSON.stringify({source,samplerHash,interpreterSHA256:'03d69e7e9e768a7e6735294f819da90d965f73d72c4134ab9ef74715d36f51bf',models:29,skipped:sum('skipped'),matched:sum('matched'),refused:sum('refused'),unexpected:sum('unexpected'),oldCountsAndDigestsIdentical:true,rows,scope:'all skipped BFS requests on unchanged finite sample schedule; only source-branded assumption RangeErrors are semantic refusals; unmetered oracle, not timing or a 15M-budget measurement'}))
