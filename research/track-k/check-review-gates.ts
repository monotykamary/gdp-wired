// Recheck completed review-follow-up receipts; no proof search.
import assert from 'node:assert/strict'
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {join} from 'node:path'
const dir=process.argv[2]!
const jobs=JSON.parse(readFileSync('research/track-k/review-gates-jobs.json','utf8')) as {name:string}[]
const rows=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(line=>{const [name,code,seconds,where]=line.split('\t');assert.equal(Number(code),0,`${name}: failed`);assert.equal(where,'boat');return {name:name!,seconds:Number(seconds)}})
assert.deepEqual(rows.map(r=>r.name).sort(),jobs.map(j=>j.name).sort(),'incomplete gate batch')
const log=(name:string)=>readFileSync(join(dir,name+'.log'),'utf8')
const paxos=[1,2,3].map(run=>{const text=log(`paxos-r${run}`);const row=text.split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l)).find(r=>r.id==='paxos_epr');assert(row&&!row.error);assert.equal(row.search.verdict,'proven');assert(row.search.ms<=60000);assert(text.includes('STRICT_EXIT=0'));return {run,ms:row.search.ms}})
let passed=0,skipped=0
for(let i=1;i<=7;i++){const text=log(`test-shard-${i}`);for(const m of text.matchAll(/^\s+(\d+) (pass|skip|fail)$/gm)){const n=Number(m[1]);if(m[2]==='fail')assert.equal(n,0);else if(m[2]==='pass')passed+=n;else skipped+=n}}
const marker=log('review-mutants').split('\n').find(l=>l.startsWith('VERIFIED_MUTANT_MATRIX='))
assert(marker,'missing complete mutant matrix')
const mutants=JSON.parse(marker.slice(marker.indexOf('=')+1)) as {id:string,survived:boolean}[]
assert.equal(mutants.length,13);assert(mutants[0]?.id==='baseline'&&mutants[0].survived)
assert.deepEqual(mutants.slice(1).filter(m=>m.survived).map(m=>m.id),['M03-slice-upper-inclusive'])
const allowed=new Set(['propext','Classical.choice','Quot.sound'])
for(const name of ['lean-count-cuts','counted-library','expanded-conformance'])for(const match of log(name).matchAll(/depends on axioms: \[([^\]]*)\]/g))for(const axiom of match[1]!.split(',').map(s=>s.trim()).filter(Boolean))assert(allowed.has(axiom),`${name}: new axiom ${axiom}`)
const files=['kernel/kernel.ts','kernel/lemma-cut.test.ts','kernel/fixtures/lemma-cut-review.json','lean-kernel/Count.lean','lean-kernel/CountMachine.lean','research/track-k/review-source/review-run.ts.txt','research/track-k/review-source/review-mutants.json']
const sourceHashes=Object.fromEntries(files.map(file=>[file,createHash('sha256').update(readFileSync(file)).digest('hex')]))
const result={jobs:rows.length,allPassed:true,paxos,shards:{passed,skipped,failed:0},mutants:{killed:11,equivalentSurvivor:'M03-slice-upper-inclusive'},sourceHashes}
writeFileSync(join(dir,'verified.json'),JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify(result,null,2))
