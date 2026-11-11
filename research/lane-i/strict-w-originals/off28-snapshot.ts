// File-only audit of the completed non-MLDR pairs; never imports a prover.
import {strict as assert} from 'node:assert'
import {readFileSync,writeFileSync,statSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
const [out,scratch,input]=process.argv.slice(2)
assert(out&&scratch&&input)
const source=readFileSync(join(input,'source.txt'),'utf8').trim(),baseline=readFileSync(join(input,'baseline-source.txt'),'utf8').trim()
const ids=JSON.parse(readFileSync(join(input,'ids.json'),'utf8')) as string[]
assert.equal(ids.length,28);assert(!ids.includes('mldr'));assert.equal(source,'8e367451ea30ed075d2f95e92660fb02e45ba459')
const sha=(b:Buffer)=>createHash('sha256').update(b).digest('hex')
const blob=(b:Buffer)=>createHash('sha1').update(`blob ${b.length}\0`).update(b).digest('hex')
const files:any[]=[],rows:any[]=[]
const record=(name:string)=>{const path=join(out,name),r={path,bytes:statSync(path).size,sha256:sha(readFileSync(path))};files.push(r);return r}
const stable=(v:any):any=>Array.isArray(v)?v.map(stable):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).filter(([k])=>!['wallMs','exclusiveWallMs'].includes(k)).map(([k,x])=>[k,stable(x)])):v
const normal=(r:any)=>stable(Object.fromEntries(Object.entries(r).filter(([k])=>!['source','target','custody'].includes(k))))
for(const id of ids){
 const pair:Record<string,any>[]=['baseline','candidate'].map(target=>{const r=JSON.parse(gunzipSync(readFileSync(join(out,id+'-'+target+'.json.gz'))).toString());assert.equal(r.id,id);assert.equal(r.target,target);assert.equal(r.source,target==='baseline'?baseline:source);assert(!r.result.error);assert.deepEqual(r.knobs,{GDP_WORK_FULL:'0',GDP_WORK_STEPS:'0'});if(r.result.proven)assert(r.result.checked);record(id+'-'+target+'.json.gz');record(id+'-'+target+'.log');return r})
 assert.deepEqual(pair[0]!.custody,pair[1]!.custody);assert.deepEqual(normal(pair[0]),normal(pair[1]),id)
 rows.push({id,verdict:pair[1]!.result.verdict,normalizedSha256:sha(Buffer.from(JSON.stringify(normal(pair[1]))))})
}
const protectedLines=readFileSync(join(input,'PROTECTED.tree'),'utf8').trim().split('\n');assert.equal(protectedLines.length,181)
for(const line of protectedLines){const m=/^\d+ blob ([a-f0-9]+)\t(.+)$/.exec(line);assert(m);for(const target of ['baseline','candidate'])assert.equal(blob(readFileSync(join(scratch,target,m[2]!))),m[1],target+':'+m[2])}
for(const target of ['baseline','candidate'])for(const name of ['extract-baseline','extract-source','extract-gdp-ts','extract-handwired','install']){if(target==='baseline'&&name==='extract-source'||target==='candidate'&&name==='extract-baseline')continue;record(target+'-'+name+'.log')}
assert.equal(files.length,120)
const summary={source,baseline,status:'PASS',scope:'completed strict28 off-mode pairs only; extra MLDR case remains outside this snapshot',exactPairs:rows.length,checked:rows.filter(r=>r.verdict==='proven').length,unknown:rows.filter(r=>r.verdict==='unknown').length,protectedFiles:181,rows,files}
const path=join(out,'strict28-snapshot.json');writeFileSync(path,JSON.stringify(summary,null,2)+'\n');console.log(JSON.stringify({path,sha256:sha(readFileSync(path)),exactPairs:summary.exactPairs,checked:summary.checked,unknown:summary.unknown,protectedFiles:181,files:120}))
