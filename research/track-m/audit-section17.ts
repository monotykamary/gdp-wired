// Audit existing pooled-run journals. No proof search or new policy.
import {readFileSync,writeFileSync,mkdtempSync} from 'node:fs'
import {join} from 'node:path'
import {homedir} from 'node:os'
import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {brotliDecompressSync} from 'node:zlib'
import {proportionalDraw} from './section17-budget.ts'
const input=process.argv[2];if(!input)throw new Error('INPUT required')
const manifest=JSON.parse(readFileSync(join(input,'archive-manifest.json'),'utf8')),bytes=readFileSync(join(input,'receipts.br')),hash=(v:string|Buffer)=>createHash('sha256').update(v).digest('hex')
assert.equal(hash(bytes),manifest.sha256)
const files:Record<string,string>=JSON.parse(brotliDecompressSync(bytes).toString()),m=JSON.parse(files['measurements.json']!),integrity=JSON.parse(files['integrity.json']!)
assert.equal(m.runs.length,12);assert.equal(m.strictWallSeconds,60)
for(const r of integrity){assert(r.kernelIdentical);assert(!r.changed.some((p:string)=>p.startsWith('kernel/')));assert.equal(hash(files[r.mode+'.js']!),r.bundleSha256)}
const near=(a:number,b:number)=>Math.abs(a-b)<=1e-6*Math.max(1,Math.abs(a),Math.abs(b)),parse=(t:string)=>t.split('\n').filter(Boolean).map(l=>JSON.parse(l)),rows:any[]=[],profiles:any[]=[],perLaw:string[]=['run,comparison,repeat,mode,law,verdict,attempts,completed,counted_units,units_complete,wall_ms']
let draws=0,fallbacks=0
for(const r of m.runs){
 const events=parse(files[r.id+'.events.jsonl']!),begin=events.find(e=>e.event==='protocol-start');assert(begin);assert.equal(begin.duration,60000);if(r.censored)assert(r.wallMs>=59000,'do not label an early crash as a watchdog stop')
 const starts=events.filter(e=>e.event==='attempt-start'),ends=events.filter(e=>e.event==='attempt-end'),ids=new Set(starts.map(e=>e.id));assert.equal(ids.size,starts.length)
 for(const e of ends){assert(ids.has(e.id));const first=starts.find(s=>s.id===e.id);assert(first&&first.law===e.law);assert(near(e.usedUnits,e.units-first.units));assert(Math.abs(e.wallMs-(e.wall-first.wall))<5)}
 let lease:any
 for(const e of events){if(e.event==='law-draw'){draws++;assert.notEqual(r.mode,'baseline');assert(near(e.grant,proportionalDraw(e.remaining,e.size,e.totalSize)));assert(e.grant>=0&&e.grant<=e.remaining/3+1e-7);assert(e.pending.includes(e.law));lease=e}
  if(e.event==='fallback-draw'){fallbacks++;assert.equal(r.mode,'combo');assert(near(e.draw,proportionalDraw(e.remaining,lease?.size??1,lease?.totalSize??1)))}
 }
 const done=events.find(e=>e.event==='protocol-end');assert.equal(!!done,r.totalUnitsComplete);if(done)assert(near(done.usedUnits,r.totalUnits))
 for(const l of r.laws){const attempts=ends.filter(e=>e.law===l.law);assert.equal(l.completed,attempts.length);assert(near(l.units,attempts.reduce((n,e)=>n+e.usedUnits,0)));assert(near(l.wallMs,attempts.reduce((n,e)=>n+e.wallMs,0)))}
 const family=events.filter(e=>e.event==='generated').flatMap(e=>e.laws),signature=hash(JSON.stringify(family))
 rows.push({id:r.id,comparison:r.comparison,repeat:r.repeat,mode:r.mode,exitCode:r.exitCode,censored:r.censored,wallMs:r.wallMs,searchWallMs:r.searchWallMs,units:r.totalUnits,unitsComplete:r.totalUnitsComplete,unattributedUnits:r.unattributedUnits,generated:r.laws.length,attempted:r.laws.filter((l:any)=>l.attempts).length,conditionalProofs:r.laws.filter((l:any)=>l.verdict==='conditional-proof').length,checked:r.laws.filter((l:any)=>l.verdict==='checked').length,overall:r.search?.search?.verdict??'censored',targets:r.targets,familySignature:signature})
 for(const l of r.laws)perLaw.push([r.id,r.comparison,r.repeat,r.mode,'"'+l.law.replaceAll('"','""')+'"',l.verdict,l.attempts,l.completed,l.units,l.unitsComplete,l.wallMs].join(','))
 const ds=events.filter(e=>e.event==='law-draw'),dispatchSpans=ds.flatMap((d,i)=>{const stop=ds[i+1]??done;return stop?[{law:d.law,grant:d.grant,units:stop.units-d.units,wallMs:stop.wall-d.wall,unitOver:stop.units-d.units-d.grant,wallOverMs:stop.wall-d.wall-d.grant}]:[]})
 profiles.push({id:r.id,laws:r.laws,draws:r.draws,dispatchSpans,events:events.filter(e=>['protocol-start','protocol-end','fallback-draw'].includes(e.event))})
}
const pairs:any[]=[];for(const comparison of ['pool','combo'])for(const repeat of [1,2,3]){const xs=rows.filter(r=>r.comparison===comparison&&r.repeat===repeat);assert.equal(xs.length,2);const baseline=xs.find(r=>r.mode==='baseline'),candidate=xs.find(r=>r.mode===comparison);assert(baseline&&candidate);pairs.push({comparison,repeat,baseline:baseline.id,candidate:candidate.id,identicalGeneratedFamily:baseline.familySignature===candidate.familySignature})}
const output=mkdtempSync(join(homedir(),'track-m-section17-audit-'));writeFileSync(join(output,'summary.json'),JSON.stringify({researchOnly:true,baseline:'5974b916',strictWallSeconds:60,formulaAudited:true,goalWeightsRecomputed:false,checkedDraws:draws,checkedFallbacks:fallbacks,rows,pairs,profiles},null,2)+'\n');writeFileSync(join(output,'per-law.csv'),perLaw.join('\n')+'\n')
console.log(JSON.stringify({output,draws,fallbacks,rows,pairs}))
const p=Bun.spawn(['bun','research/track-m/pack-section10-archive.ts',join(output,'summary.json'),join(output,'per-law.csv')],{stdout:'inherit',stderr:'inherit'});if(await p.exited)throw new Error('packing failed')
