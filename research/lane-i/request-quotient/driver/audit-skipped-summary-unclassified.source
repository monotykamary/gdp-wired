import {strict as a} from 'node:assert'
import {readFileSync,readdirSync} from 'node:fs'
import {join} from 'node:path'
const [dir,source,samplerHash]=process.argv.slice(2)
const files=readdirSync(dir!).filter(f=>f.startsWith('quotient-audit-skips-')&&f.endsWith('.log')).sort();a.equal(files.length,29)
const rows=files.map(file=>{
 const lines=readFileSync(join(dir!,file),'utf8').split('\n').filter(l=>l.startsWith('QUOTIENT_SKIPPED_AUDIT '));a.equal(lines.length,1,file)
 const r=JSON.parse(lines[0]!.slice('QUOTIENT_SKIPPED_AUDIT '.length));a.equal(r.id,file.slice('quotient-audit-skips-'.length,-4));a.equal(r.source,source);a.equal(r.originalSamplerSHA256,samplerHash);a.equal(r.adapterEdits,2);a.equal(r.skipped,r.matched+r.refused)
 a.equal(r.rows.reduce((n:number,p:any)=>n+p.skipped,0),r.skipped);a.equal(r.rows.reduce((n:number,p:any)=>n+p.matched,0),r.matched);a.equal(r.rows.reduce((n:number,p:any)=>n+p.refused,0),r.refused)
 return {id:r.id,skipped:r.skipped,matched:r.matched,refused:r.refused,kept:r.kept,rows:r.rows}
})
a(rows.some(r=>r.id==='mldr'&&r.skipped>0))
const sum=(key:'skipped'|'matched'|'refused')=>rows.reduce((n,r)=>n+r[key],0)
console.log('QUOTIENT_SKIPPED_SUMMARY '+JSON.stringify({source,samplerHash,models:29,skipped:sum('skipped'),matched:sum('matched'),refused:sum('refused'),rows,scope:'all skipped BFS requests on the unchanged finite sample schedule; oracle run is not a timing or 15M-budget measurement'}))
