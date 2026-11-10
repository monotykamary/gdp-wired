// Read-only receipt audit; no prover/test reruns and no timeout changes.
import{strict as assert}from'node:assert'
import{readFileSync,readdirSync}from'node:fs'
import{join}from'node:path'
import{createHash}from'node:crypto'
import{gunzipSync}from'node:zlib'
import{stripVTControlCharacters}from'node:util'
const inputRoot=process.argv[2];if(!inputRoot)throw Error('evidence root required');const root=inputRoot
const inputHashes:Record<string,string>={}
const sha=(x:string|Uint8Array)=>createHash('sha256').update(x).digest('hex'),read=(p:string)=>{const bytes=readFileSync(join(root,p));inputHashes[p]=sha(bytes);return bytes.toString()},events=(s:string,tag:string):any[]=>s.split('\n').filter(l=>l.startsWith(tag+' ')).map(l=>JSON.parse(l.slice(tag.length+1)))
const cohorts:any[]=[],skips:any[]=[],failures:any[]=[]
for(const group of ['initial','phased','epyc']){
 const dir=join(root,group);let files:string[];try{files=readdirSync(dir)}catch{continue}
 const placement=JSON.parse(read(group+'/placement.json')),manifest=JSON.parse(read(group+'/input-manifest.json')),terminal=read(group+'/summary.tsv').trim().split('\n').map(l=>l.split('\t'))
 for(const file of files.filter(f=>f.endsWith('.log'))){const name=file.slice(0,-4);if(name==='follow-up-commitlint')continue
  const text=read(group+'/'+file),adm=events(text,'REGRESSION_ADMISSION');assert.equal(adm.length,1,name);const a=adm[0],p=placement[name];assert.equal(a.name,name);assert.equal(p.cpu,a.cpu);assert(p.exclusive&&p.co_tenants===0);const done=terminal.filter(r=>r[0]===name);assert.equal(done.length,1);assert.equal(done[0]![1],'0')
  const sources=events(text,'REGRESSION_SOURCE'),runs=events(text,'REGRESSION_RUN'),pairs=events(text,'REGRESSION_PAIR'),summary=events(text,'REGRESSION_SUMMARY'),clean=events(text,'REGRESSION_CLEAN')
  if(!a.eligible){assert.equal(events(text,'REGRESSION_CPU_SKIP').length,1);assert.equal(sources.length+runs.length+pairs.length+summary.length,0);skips.push({group,name,cpu:a.cpu});continue}
  assert.equal(sources.length,2);assert.deepEqual(sources.map(s=>String(s.side)).sort((a,b)=>a.localeCompare(b)),['base','candidate']);assert.equal(runs.length,10);assert.equal(pairs.length,5);assert.equal(summary.length,1);assert.equal(clean.length,2);assert(clean.every(x=>x.dirty===''))
  for(const s of sources){assert.equal(s.cpu,a.cpu);assert.equal(s.revision,s.side==='base'?manifest.base:manifest.candidate);assert.deepEqual(s.sources,manifest.sources[s.side]);assert(s.meta.clean)}
  const normalized:any[]=[]
  for(let repeat=1;repeat<=5;repeat++){
   const matching=pairs.filter(x=>x.repeat===repeat);assert.equal(matching.length,1);const pair=matching[0],order=repeat%2?['candidate','base']:['base','candidate'];assert.deepEqual(pair.order,order);const out:Record<string,any>={}
   for(const side of order){const found=runs.filter(x=>x.repeat===repeat&&x.side===side);assert.equal(found.length,1);const r=found[0];assert.equal(r.cpu,a.cpu);assert.equal(r.revision,side==='base'?manifest.base:manifest.candidate)
    const data=gunzipSync(Buffer.from(r.traceGzipBase64,'base64'),{maxOutputLength:16*1024*1024}).toString(),marker='\n---stderr---\n',cut=data.lastIndexOf(marker);assert(cut>=0);const stdout=data.slice(0,cut),stderr=data.slice(cut+marker.length);assert.equal(sha(stdout),r.stdoutSha256);assert.equal(sha(stderr),r.stderrSha256)
    const resource=JSON.parse(gunzipSync(Buffer.from(r.resourcesGzipBase64,'base64')).toString()),plain=stripVTControlCharacters(stdout+'\n'+stderr);let passed=false,detail:any
    if(a.mode.startsWith('two-phase')){assert.deepEqual(r.args,['--preload','./regression-phase-preload.ts','research/protocols/ic3syn/run.ts','--ms','60000','--only','two_phase_commit','--skip','broken']);const native=stdout.split('\n').flatMap(l=>{try{return[JSON.parse(l)]}catch{return[]}}).filter(x=>x.id==='two_phase_commit');assert.equal(native.length,1);assert.deepEqual(r.protocol,native[0]);passed=r.exit===0&&native[0].search?.verdict==='proven';const phases=stderr.split('\n').flatMap(l=>{if(!l.startsWith('[infer] '))return[];const i=l.indexOf('{');if(i<0)return[];return[{phase:l.slice(8,i).trim(),...JSON.parse(l.slice(i))}]});if(group==='phased'||group==='epyc')assert(phases.length>0,'missing requested phase timings');detail={verdict:native[0].search?.verdict,rootMs:native[0].search?.ms,work:native[0].search?.work,full:native[0].search?.full,phases}}
    else{assert.deepEqual(r.args,a.mode==='infer'?['test','./core/infer.test.ts','--test-name-pattern','an invariant over four values']:['test','./core/sums.test.ts']);const count=(word:string)=>Number([...plain.matchAll(new RegExp('^\\s*(\\d+) '+word+'\\s*$','gm'))].at(-1)?.[1]??NaN),pass=count('pass'),fail=count('fail'),expected=a.mode==='infer'?1:7;assert.equal(pass+fail,expected,'incomplete native test selection');assert.equal(r.exit,fail===0?0:1);passed=r.exit===0;const cases=plain.split('\n').filter(l=>l.includes('(pass)')||l.includes('(fail)'));detail={pass,fail,cases}}
    assert.equal(r.passed,passed);assert.equal(pair.outcomes[side].passed,passed);assert.equal(pair.outcomes[side].exit,r.exit);assert.equal(pair.outcomes[side].wallMs,r.wallMs);out[side]={passed,exit:r.exit,wallMs:r.wallMs,peakRssKiB:resource.peakRssKiB,oomDelta:resource.oomDelta,...detail}
   }
   const loss=out.base.passed&&!out.candidate.passed;assert.equal(pair.candidateOnlyLoss,loss);normalized.push({repeat,order,...out,candidateOnlyLoss:loss})
  }
  const basePass=normalized.filter(r=>r.base.passed).length,candidatePass=normalized.filter(r=>r.candidate.passed).length,losses=normalized.filter(r=>r.candidateOnlyLoss).map(r=>r.repeat);assert.equal(summary[0].basePass,basePass);assert.equal(summary[0].candidatePass,candidatePass);assert.deepEqual(summary[0].candidateOnlyLosses,losses)
  const result={group,name,mode:a.mode,cpu:a.cpu,vm:p.vm,basePass,candidatePass,candidateOnlyLosses:losses,majorityLoss:losses.length>=3,pairs:normalized};cohorts.push(result);if(result.majorityLoss)failures.push({group,name,losses})
 }
}
const epyc=cohorts.filter(x=>x.cpu==='AMD EPYC 4585PX 16-Core Processor'&&x.mode.startsWith('two-phase')).sort((a,b)=>a.name.localeCompare(b.name)),other=cohorts.filter(x=>x.group==='phased'&&x.cpu!=='AMD EPYC 4585PX 16-Core Processor').sort((a,b)=>a.name.localeCompare(b.name)),infer=cohorts.filter(x=>x.mode==='infer'),sums=cohorts.filter(x=>x.mode==='sums')
assert.equal(infer.length,1);assert.equal(sums.length,1)
const result={auditSourceSha256:sha(readFileSync(import.meta.path)),inputHashes,primaryEpyc:epyc[0]?.name??null,primaryOther:other[0]?.name??null,requiredCpuCoverage:epyc.length>0&&other.length>0,majorityRegressions:failures,cohorts,skips,scope:'original a8/base sources; no production change or final gate claim'}
console.log('REGRESSION_RECEIPT_AUDIT '+JSON.stringify(result));if(!result.requiredCpuCoverage)process.exitCode=2
