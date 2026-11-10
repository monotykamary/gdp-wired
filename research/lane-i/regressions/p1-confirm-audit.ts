import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {brotliDecompressSync,gunzipSync} from 'node:zlib'
import {join} from 'node:path'
const dir=process.argv[2],familyPath=process.argv[3];if(!dir||!familyPath)throw Error('confirmation directory and frozen family required')
const hash=(v:string|Uint8Array)=>createHash('sha256').update(v).digest('hex'),same=(a:unknown,b:unknown)=>JSON.stringify(a)===JSON.stringify(b),issues:string[]=[],check=(b:unknown,s:string)=>{if(!b)issues.push(s)}
const log=readFileSync(join(dir,'p1-fixed-confirm-7006.log'),'utf8'),lines=log.split('\n'),hs=lines.filter(l=>l.startsWith('P1_CONFIRM_ARCHIVE ')),bs=lines.filter(l=>l.startsWith('P1_CONFIRM_RESULT_BR '))
if(hs.length!==1||bs.length!==1)throw Error('complete archive missing')
const header=JSON.parse(hs[0]!.slice(19)),encoded=bs[0]!.slice(21),bytes=Buffer.from(encoded,'base64')
if(header.sha256!==hash(bytes)||header.encodedBytes!==encoded.length)throw Error('archive integrity')
const r=JSON.parse(brotliDecompressSync(bytes).toString()),manifest=JSON.parse(readFileSync(join(dir,'input-manifest.json'),'utf8')),familyText=readFileSync(familyPath,'utf8'),family=JSON.parse(familyText),place=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8'))['p1-fixed-confirm-7006']
check(same(r.config,manifest.config)&&r.inputManifestSha256===manifest.manifestSha256,'admitted input')
check(r.config.candidate==='d3adf3c9589ec014a158b6f42ecfb091c999bb43'&&r.config.fixed==='f7c5b4bad58578d95684ca279e882f48fabd8525','requested revisions')
const status=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\t'),backend=JSON.parse(readFileSync(join(dir,'backends.json'),'utf8'))
check(status[0]==='p1-fixed-confirm-7006'&&status[1]==='0'&&status[3]==='boat'&&backend.where?.boat===1&&!backend.fallbacks?.length,'execution')
check(hash(familyText)===r.config.p1Sha256,'frozen family')
check(place.exclusive&&place.co_tenants===0&&place.cpu===r.cpu,'placement')
check(r.sources.length===2&&r.records.length===10,'cardinality')
for(const s of r.sources){const current=s.side==='current';check(s.side==='current'||s.side==='fixed','source label');check(s.revision===(current?r.config.candidate:r.config.fixed)&&s.meta.revision===s.revision&&s.meta.clean,'source identity');check(s.counts===(current?r.config.candidateCounts:r.config.fixedCounts),'count source');check(same(s.kernel,r.sources[0].kernel)&&Object.keys(s.kernel).length===4,'kernel or law change')}
const seen=new Set<string>(),rows:any[]=[]
for(const row of r.records){const id=`${row.repeat}/${row.side}`;check(!seen.has(id)&&row.repeat>=1&&row.repeat<=5&&Number.isInteger(row.repeat),'repeat identity');seen.add(id)
 const s=r.sources.find((s:any)=>s.side===row.side);check(s&&row.revision===s.revision,'row source')
 const p=row.summary,a=JSON.parse(row.audit.stdout||'{}'),cap=JSON.parse(gunzipSync(Buffer.from(row.proofGzip,'base64')).toString()),expected=row.side==='current'?2046.9378360:1152.3382236
 check(row.audit.exit===0&&a.checked&&a.familyVerified&&a.originalHarness,'native p1 replay '+id)
 check(p.checked&&p.withinDiagnosticLine&&p.budget===6000&&p.wallAllowance===7000&&same(p.passOrder,[1,0])&&p.suppliedLaws.length===0&&Math.abs(p.units-expected)<1e-6,'p1 cost '+id)
 check(same(cap.record,p)&&same(cap.m,family.m)&&same(cap.laws,family.laws)&&cap.proof,'original proof capture '+id)
 const whole=row.whole,parsed=whole.stdout.split('\n').flatMap((l:string)=>{try{return[JSON.parse(l)]}catch{return[]}}).filter((v:any)=>v.id==='paxos_epr')
 check(whole.exit===0&&same(parsed,whole.results)&&parsed.length===1&&parsed[0].search?.verdict==='proven'&&parsed[0].search.work===6915544&&parsed[0].search.full===1037946,'whole Paxos '+id)
 rows.push({repeat:row.repeat,side:row.side,p1Units:p.units,solver:parsed[0]?.search?.work,full:parsed[0]?.search?.full})
}
for(let i=1;i<=5;i++)for(const side of ['current','fixed'])check(seen.has(`${i}/${side}`),'missing pair')
const result={issues,baseline:r.config.candidate,candidate:r.config.fixed,cpu:r.cpu,pairs:5,rows,qualified:issues.length===0,scope:'Exact-commit cost confirmation, not a final gate',finalGate:false}
writeFileSync(join(dir,'audit.json'),JSON.stringify(result,null,2)+'\n');writeFileSync(join(dir,'result.json.br'),bytes);console.log(JSON.stringify(result));if(issues.length)process.exitCode=1
