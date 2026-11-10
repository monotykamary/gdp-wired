import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {brotliDecompressSync,gunzipSync} from 'node:zlib'
const hash=(v:string|Uint8Array)=>createHash('sha256').update(v).digest('hex')
export function readSchedulingReceipt(log:string){
 const rows=log.split('\n'),headers=rows.filter(x=>x.startsWith('P1_SCHEDULING_ARCHIVE ')),bodies=rows.filter(x=>x.startsWith('P1_SCHEDULING_RESULT_BR '))
 if(headers.length!==1||bodies.length!==1)throw Error('one complete archive required')
 const h=JSON.parse(headers[0]!.slice(22)),encoded=bodies[0]!.slice(24),bytes=Buffer.from(encoded,'base64')
 if(h.sha256!==hash(bytes)||h.encodedBytes!==encoded.length)throw Error('archive digest or length mismatch')
 return JSON.parse(brotliDecompressSync(bytes).toString())
}
// Receipts are already native-replayed on boat. This independent pass binds the
// raw captures, admitted hashes, exact attempt cardinality and joint work claim.
export function auditScheduling(r:any,manifest:any,family:any){
 const issues:string[]=[],check=(ok:unknown,message:string)=>{if(!ok)issues.push(message)},same=(a:unknown,b:unknown)=>JSON.stringify(a)===JSON.stringify(b)
 check(same(r.config,manifest.config),'configuration');check(r.inputManifestSha256===manifest.manifestSha256,'input manifest')
 check(Object.values(manifest.files).includes(r.driverSha256),'driver hash')
 check(r.familyHashes?.p1===r.config.p1Sha256&&r.familyHashes?.paxos===r.config.paxosSha256,'family hashes')
 const names=r.sources.map((s:any)=>s.name),policy=names.find((s:string)=>s!=='control'&&s!=='current')
 check(names.length===3&&new Set(names).size===3&&names.includes('control')&&names.includes('current')&&policy,'source cardinality')
 for(const s of r.sources){const control=s.name==='control',rev=control?r.config.control:r.config.candidate,expected=control?r.config.controlCounts:r.config.candidateCounts
  check(s.revision===rev&&s.meta?.revision===rev&&s.meta.clean===true,s.name+': source identity')
  check(s.countsBefore===expected,s.name+': count source');check(s.name===policy?s.experimental&&s.countsAfter!==expected:s.countsAfter===expected,s.name+': source patch')
  check(same(s.kernelHashes,r.sources[0].kernelHashes)&&Object.keys(s.kernelHashes).length===3,s.name+': kernel changed')
 }
 check(r.records.length===r.config.repeats*3,'record cardinality');const ids=new Set<string>(),units:Record<string,number[]>={}
 for(const row of r.records){const id=`${row.source}/${row.repeat}`;check(!ids.has(id),'duplicate '+id);ids.add(id)
  check(names.includes(row.source)&&Number.isInteger(row.repeat)&&row.repeat>=1&&row.repeat<=r.config.repeats,'record identity '+id)
  const p=row.p1.summary,a=JSON.parse(row.p1.audit.stdout),cap=JSON.parse(gunzipSync(Buffer.from(row.p1.compactCaptureGzip,'base64')).toString())
  check(row.p1.audit.exit===0&&a.checked&&a.familyVerified&&a.originalHarness,id+': independent p1 replay')
  check(p.checked&&p.withinDiagnosticLine&&p.conditional&&p.generatorOnly&&p.budget===6000&&p.wallAllowance===7000&&same(p.suppliedLaws,[])&&same(p.passOrder,[1,0]),id+': p1 contract')
  check(same(cap.record,p)&&same(cap.m,family.m)&&same(cap.laws,family.laws)&&cap.proof,id+': p1 capture')
  check(a.units===p.units&&Number.isFinite(p.units)&&p.units>0&&p.units<=6000,id+': p1 units')
  ;(units[row.source]??=[]).push(p.units)
  const px=row.paxos.trace;check(px.familySha256===r.config.paxosSha256&&px.cpu?.trim()===r.cpu,id+': Paxos identity')
  if(row.source!=='control'){const a=JSON.parse(row.paxos.audit?.stdout??'{}')
   check(px.outcome==='proof'&&same(px.checks,['checked','checked'])&&row.paxos.audit?.exit===0&&a.checkedGoals===2&&a.familySha256===px.familySha256,id+': Paxos replay')
   check(px.solver===38917&&Math.abs(px.full-26285.6192)<1e-6&&px.completed.length===0,id+': frozen Paxos work')
  }
 }
 for(const name of names){check(units[name]?.length===r.config.repeats,name+': repeat count');check(Math.max(...(units[name]??[]))-Math.min(...(units[name]??[]))<1e-6,name+': unstable p1 work')}
 check(units.control?.every(n=>Math.abs(n-1152.3382236)<1e-6),'validated control cost')
 const whole=r.whole.map((row:any)=>{const parsed=row.stdout.split('\n').flatMap((line:string)=>{try{return[JSON.parse(line)]}catch{return[]}}).filter((v:any)=>v.id==='paxos_epr')
  check(row.exit===0&&same(parsed,row.results)&&parsed.length===1&&parsed[0].search?.verdict==='proven',row.source+': whole Paxos result')
  return{source:row.source,...row.results[0]?.search}
 })
 check(whole.length===2&&new Set(whole.map((w:any)=>w.source)).size===2&&whole.some((w:any)=>w.source==='current')&&whole.some((w:any)=>w.source===policy),'whole cardinality')
 const base=whole.find((w:any)=>w.source==='current'),candidate=whole.find((w:any)=>w.source===policy),p1Restored=units[policy]?.every(n=>Math.abs(n-(units.control?.[0]??NaN))<1e-6),p1Regression=units.current?.every(n=>n>(units.control?.[0]??NaN))
 const paxosFullDelta=candidate?.full-base?.full,paxosSolverDelta=candidate?.work-base?.work
 return{issues,policy,cpu:r.cpu,p1Units:units,p1Regression,p1Restored,paxosFullDelta,paxosSolverDelta,jointCriterion:issues.length===0&&p1Regression&&p1Restored&&paxosFullDelta===0&&paxosSolverDelta===0,whole,finalGate:false}
}
if(import.meta.main){const [log,manifest,family,out]=process.argv.slice(2);if(!log||!manifest||!family||!out)throw Error('log manifest family output required');const result=auditScheduling(readSchedulingReceipt(readFileSync(log,'utf8')),JSON.parse(readFileSync(manifest,'utf8')),JSON.parse(readFileSync(family,'utf8')));writeFileSync(out,JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify(result));if(result.issues.length)process.exitCode=1}
