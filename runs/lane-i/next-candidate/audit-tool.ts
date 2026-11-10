import{readFileSync,readdirSync}from'node:fs'
import{join,posix}from'node:path'
import{gunzipSync,gzipSync}from'node:zlib'
import{createHash}from'node:crypto'
import assert from'node:assert/strict'
const sha=(v:string|Uint8Array)=>createHash('sha256').update(v).digest('hex'),dir=process.argv[2]!,load=(f:string)=>readFileSync(join(dir,f),'utf8'),json=(f:string)=>JSON.parse(load(f))
function decode(r:any){const text=gunzipSync(Buffer.from(r.traceGzipBase64,'base64')).toString(),at=text.indexOf('\n---stderr---\n');if(at<0)throw Error('separator');const stdout=text.slice(0,at),stderr=text.slice(at+14);if(sha(stdout)!==r.stdoutSha256||sha(stderr)!==r.stderrSha256)throw Error('digest');return{stdout,stderr}}
const fixture={traceGzipBase64:gzipSync('out\n---stderr---\nerr').toString('base64'),stdoutSha256:sha('out'),stderrSha256:sha('err')}
assert.deepEqual(decode(fixture),{stdout:'out',stderr:'err'});assert.throws(()=>decode({...fixture,stdoutSha256:'wrong'}));assert.throws(()=>decode({...fixture,traceGzipBase64:gzipSync('no separator').toString('base64')}))
const config=json('frozen-config.json'),manifest=json('input-manifest.json'),placement=json('placement.json'),backend=json('backends.json'),integrityIssues:string[]=[],blockers:string[]=[],jobs:any[]=[],p1:any[]=[],paxos:any[]=[],tip:any[]=[],evidenceHashes:Record<string,string>={}
if(sha(load('frozen-config.json'))!==manifest.files['gate-inputs/gate.json'])integrityIssues.push('frozen config hash')
if(backend.where?.boat!==14||backend.fallbacks?.length)integrityIssues.push('backend roster')
const rows=load('summary.tsv').trim().split('\n').map(l=>l.split('\t'));if(rows.length!==14||new Set(rows.map(r=>r[0])).size!==14)integrityIssues.push('job cardinality')
for(const [name,exit,,where]of rows){const file=name+'.log',text=load(file),lines=text.split('\n'),mode=name.replace('next-',''),inputs=lines.filter(l=>l.startsWith('NEXT_INPUT ')).map(l=>JSON.parse(l.slice(11))),sources=lines.filter(l=>l.startsWith('NEXT_SOURCE ')).map(l=>JSON.parse(l.slice(12))),steps:any[]=[],nativeFiles=new Set<string>();evidenceHashes[file]=sha(text)
 if(where!=='boat'||!placement[name!]?.exclusive||placement[name!]?.co_tenants!==0)integrityIssues.push(name+': placement')
 if(exit!=='0')blockers.push(name+': worker exit '+exit)
 if(name!=='next-commitlint'&&(inputs.length!==1||inputs[0].manifest!==manifest.manifestSha256||inputs[0].config.candidate!==config.candidate||inputs[0].config.baseline!==config.baseline))integrityIssues.push(name+': input identity')
 for(const s of sources){const side=s.side;if(!['base','candidate'].includes(side)||s.meta.revision!==(side==='base'?config.baseline:config.candidate)||!s.meta.clean||JSON.stringify(s.source)!==JSON.stringify(config.sources[side])||JSON.stringify(s.harness)!==JSON.stringify(config.originalHarness))integrityIssues.push(name+': source')}
 for(const line of lines){
  if(line.startsWith('NEXT_CLEAN ')){if(JSON.parse(line.slice(11)).tracked)integrityIssues.push(name+': tracked mutation')}
  else if(line.startsWith('NEXT_STEP ')){const r=JSON.parse(line.slice(10));try{const raw=decode(r),counts={pass:0,fail:0,skip:0,assertions:0};let cwd='';for(const l of raw.stderr.split('\n')){const cmd=/^\$ (?:\(cd ([^)]+)\) )?bun /.exec(l);if(cmd)cwd=cmd[1]??'';const f=/^([\w./-]+\.test\.ts):$/.exec(l);if(f){const p=posix.normalize(posix.join(cwd,f[1]!));nativeFiles.add(p)}const c=/^\s*(\d+) (pass|fail|skip)\s*$/.exec(l);if(c)counts[c[2]as'pass'|'fail'|'skip']+=Number(c[1]);const a=/^\s*(\d+) expect\(\) calls\s*$/.exec(l);if(a)counts.assertions+=Number(a[1])}
   steps.push({label:r.label,exit:r.exit,signal:r.signal,classification:r.resources.classification,peakRssKiB:r.resources.peakRssKiB,oomDelta:r.resources.oomDelta,kernelPidOom:r.resources.kernelPidOom,counts})
   if(counts.fail)blockers.push(name+': '+counts.fail+' native test failures')
  }catch(e){integrityIssues.push(name+': '+String(e))}}
  else if(line.startsWith('NEXT_P1 ')){const r=JSON.parse(line.slice(8));if(!r.checked.checked||!r.checked.familyVerified||Math.abs(r.summary.units-1152.3382236)>1e-6)blockers.push('p1 replay/cost');p1.push({repeat:r.repeat,units:r.summary.units,checked:r.checked.checked})}
  else if(line.startsWith('NEXT_PAXOS ')){const r=JSON.parse(line.slice(11));for(const v of r.rows){if(v.search.verdict!=='proven'||v.search.work!==6915544||v.search.full!==1037946)blockers.push('Paxos work/result');paxos.push({repeat:r.repeat,verdict:v.search.verdict,work:v.search.work,full:v.search.full})}}
  else if(line.startsWith('BAR_PAIR ')){const r=JSON.parse(line.slice(9));if(r.task!=='tip2015/relaxedprefix_correct.smt2'||r.strictSeconds!==60||r.meta.base.revision!==config.baseline||r.meta.candidate.revision!==config.candidate)integrityIssues.push('TIP identity');for(const side of ['base','candidate']){const o=r.outcomes[side];try{decode(o)}catch(e){integrityIssues.push('TIP archive '+String(e))}tip.push({repeat:r.repeat,side,answer:o.answer,exit:o.exit,classification:o.resources.classification,peakRssKiB:o.resources.peakRssKiB,oomDelta:o.resources.oomDelta});if(o.exit!==0)blockers.push('TIP '+side+'/'+r.repeat+': exit '+o.exit)}}
 }
 const missing=name==='next-new-tests'?config.newTests.map((p:string)=>posix.normalize(p)).filter((p:string)=>!nativeFiles.has(p)):[];if(missing.length)blockers.push('targeted files not observed: '+missing.join(', '))
 jobs.push({name,exit:Number(exit),mode,steps,nativeFiles:[...nativeFiles].sort(),requestedButUnobserved:missing})
}
if(p1.length!==3||paxos.length!==3||tip.length!==6)integrityIssues.push('protocol record cardinality')
for(const file of readdirSync(dir))if(/\.json$|\.tsv$/.test(file))evidenceHashes[file]=sha(load(file))
console.log('NEXT_PACKET_SUMMARY '+JSON.stringify({candidate:config.candidate,baseline:config.baseline,integrityIssues,blockers,jobs,p1,paxos,tip,evidenceHashes,fixtures:3,archiveIntegrity:integrityIssues.length===0,preflightAccepted:integrityIssues.length===0&&blockers.length===0,finalGate:false}))
if(integrityIssues.length)process.exitCode=1
