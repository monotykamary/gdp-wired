import{readFileSync,readdirSync}from'node:fs'
import{join,posix}from'node:path'
import{createHash}from'node:crypto'
import{gunzipSync,gzipSync}from'node:zlib'
import assert from'node:assert/strict'
const root=process.argv[2]!,read=(p:string)=>readFileSync(join(root,p),'utf8'),json=(p:string)=>JSON.parse(read(p)),sha=(x:string|Uint8Array)=>createHash('sha256').update(x).digest('hex')
function decode(r:any){const text=gunzipSync(Buffer.from(r.traceGzipBase64,'base64')).toString(),at=text.indexOf('\n---stderr---\n');assert(at>=0);const stdout=text.slice(0,at),stderr=text.slice(at+14);assert.equal(sha(stdout),r.stdoutSha256);assert.equal(sha(stderr),r.stderrSha256);return{stdout,stderr}}
const f={traceGzipBase64:gzipSync('a\n---stderr---\nb').toString('base64'),stdoutSha256:sha('a'),stderrSha256:sha('b')};assert.deepEqual(decode(f),{stdout:'a',stderr:'b'});assert.throws(()=>decode({...f,stdoutSha256:'wrong'}));assert.throws(()=>decode({...f,traceGzipBase64:gzipSync('bad').toString('base64')}))
const c2=json('config2.json'),c3=json('config3.json'),parent=sha(read('parent-kernel.ts')),records=(p:string,tag:string)=>read(p).split('\n').filter(l=>l.startsWith(tag+' ')).map(l=>JSON.parse(l.slice(tag.length+1)))
function sources(file:string,c:any){for(const r of records(file,'NEXT_SOURCE')){assert.equal(r.meta.revision,r.side==='base'?c.baseline:c.candidate);assert.equal(r.meta.clean,true);assert.deepEqual(r.source,c.sources[r.side]);assert.deepEqual(r.harness,c.originalHarness)}}
sources('v2/next-v2-targeted.log',c2);sources('v3/next-v3-check.log',c3)
const target=records('v2/next-v2-targeted.log','NEXT_STEP');assert.equal(target.length,1);assert.equal(target[0].exit,0);assert.deepEqual(target[0].args,['test',...c2.newTests]);const raw=decode(target[0]),files=[...raw.stderr.matchAll(/^([\w./-]+\.test\.ts):$/gm)].map(m=>posix.normalize(m[1]!))
assert.equal(files.length,25);assert.deepEqual([...new Set(files)].sort(),c2.newTests.map((p:string)=>posix.normalize(p)).sort());assert.match(raw.stderr,/163 pass/);assert.match(raw.stderr,/0 fail/);assert.match(raw.stderr,/11974 expect\(\) calls/)
const check=records('v3/next-v3-check.log','NEXT_STEP');assert.equal(check.length,1);assert.equal(check[0].exit,0);assert.deepEqual(check[0].args,['run','check']);const checked=decode(check[0]);assert.match(checked.stdout,/Found 0 warnings and 0 errors/)
const pairs:any[]=[]
for(const file of readdirSync(join(root,'v2')).filter(f=>f.startsWith('effect-'))){sources('v2/'+file,c2);for(const s of records('v2/'+file,'NEXT_STEP'))decode(s);pairs.push(...records('v2/'+file,'NEXT_EFFECT'))}
assert.equal(pairs.length,4);const isolated=pairs.filter(p=>p.kind==='isolated');assert.equal(isolated.length,3);assert.equal(isolated.filter(p=>p.outcomes.base.exit===0).length,3);assert.equal(isolated.filter(p=>p.outcomes.candidate.exit===0).length,2)
const traces:any[]=[]
for(let n=1;n<=3;n++){
 const rs=records('v3/effect-trace-'+n+'.log','EFFECT_SOURCE_TRACE');assert.equal(rs.length,5);assert.equal(new Set(rs.map(r=>r.variant)).size,5)
 for(const r of rs){assert.equal(r.repeat,n);assert.equal(r.meta.clean,true);assert.equal(r.meta.revision,r.revision);assert.equal(r.nativeKernel,c3.sources.base['kernel/kernel.ts']);assert.equal(r.exit,0);const exp=r.variant==='prior-binder'||r.variant==='unshared-rows';assert.equal(r.experimental,exp);assert.equal(r.before,r.variant==='base'?c3.sources.base['kernel/prove.ts']:r.variant==='parent'?parent:c3.sources.candidate['kernel/prove.ts']);assert.equal(r.after,r.variant==='prior-binder'?parent:r.before);assert.equal(r.rowsShared,r.variant==='unshared-rows'?'0':'default');assert.equal(r.tracked,r.variant==='prior-binder'?'M kernel/prove.ts':'');decode(r);const q=gunzipSync(Buffer.from(r.queriesGzipBase64,'base64')).toString();assert.equal(sha(q),r.queriesSha256);assert.equal(q.trim().split('\n').filter(Boolean).length,r.queryCount);JSON.parse(gunzipSync(Buffer.from(r.goalsGzipBase64,'base64')).toString());traces.push({repeat:n,variant:r.variant,revision:r.revision,laws:r.outcome.rules.flatMap((x:any)=>x.laws.map((l:any)=>({name:l.name,verdict:l.verdict})))})}
}
const passed=(name:string)=>traces.filter(r=>r.variant===name&&r.laws.length===3&&r.laws.every((l:any)=>l.verdict==='proven')).length
assert.equal(passed('base'),3);assert.equal(passed('candidate'),3);assert.equal(passed('parent'),2)
console.log('FINAL_PACKET_AUDIT '+JSON.stringify({candidate:c3.candidate,baseline:c3.baseline,integrity:true,fixtures:3,targeted:{files:25,pass:163,fail:0,assertions:11974},check:{exit:0,peakRssKiB:check[0].resources.peakRssKiB,oomDelta:check[0].resources.oomDelta},pairs,traces,knownFailuresRetained:true,finalGate:false}))
