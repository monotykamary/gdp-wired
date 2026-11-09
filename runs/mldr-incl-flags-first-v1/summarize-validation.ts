// Artifact integrity summary only. Does not replay proofs or accept a merge gate.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {brotliDecompressSync} from 'node:zlib'
const dir=process.argv[2]!, sha=(x:string|Buffer)=>createHash('sha256').update(x).digest('hex')
const rows=(name:string)=>readFileSync(`${dir}/${name}.log`,'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l))
const all=rows('fresh-conditional-and-replay'), generation=all.filter(r=>r.artifact==='mldr-incl-capture')
if(generation.length!==1||generation[0].revision!=='9124348d5d313ab7e89082b0146a72d6a7c8bf66'||generation[0].queries!==0)throw Error('generation provenance')
function unpack(row:any){const bytes=Buffer.from(row.data,'base64');if(sha(bytes)!==row.sha256||row.omitted!==0)throw Error('archive integrity');return JSON.parse(brotliDecompressSync(bytes).toString()) as Record<string,string>}
const generated=unpack(generation[0])['family-first.json']!, family=JSON.parse(generated)
if(family.laws.length!==34)throw Error('family roster')
const tests=JSON.parse(readFileSync(`${dir}/focused-tests.json`,'utf8'))
const collection=JSON.parse(readFileSync(`${dir}/file-collection.json`,'utf8'))
const expected=['fresh-conditional-and-replay','integrated-check','original-r1','original-r2','original-r3']
if(!collection.done||collection.running||collection.queued||JSON.stringify(collection.rows.map((r:any)=>r.name).sort())!==JSON.stringify(expected)||collection.rows.some((r:any)=>r.code!==0))throw Error('batch incomplete')
const cases=[]
for(let i=0;i<all.length;i++){
 const r=all[i];if(!r.variant)continue
 const next=all.findIndex((p,j)=>j>i&&p.variant), end=next<0?all.length:next, segment=all.slice(i+1,end)
 const captures=segment.filter(p=>p.artifact==='mldr-incl-production-capture'), replays=segment.filter(p=>p.diagnostic&&p.goal)
 if(!r.conditional||r.family!=='captured generated family (no hand law)'||!r.proven||!r.checked||r.supportCount!==0||r.laws!==34||r.checks.length!==2||!r.checks.every((c:any)=>c.checked&&c.treeChecked))throw Error('conditional check record')
 if(replays.length!==2||!replays.every(p=>p.checked)||new Set(replays.map(p=>p.goal)).size!==2||captures.length!==1)throw Error('replay record')
 const files=unpack(captures[0]), names=Object.keys(files).sort()
 if(JSON.stringify(names)!==JSON.stringify(['family-source.json','final-proof-0.json','final-proof-1.json','production-proof.json'])||files['family-source.json']!==generated)throw Error('incomplete or wrong source archive')
 const proof=JSON.parse(files['production-proof.json']!)
 if(proof.law!==r.law||JSON.stringify(proof.machine)!==JSON.stringify(family.machine)||JSON.stringify(proof.laws)!==JSON.stringify(family.laws))throw Error('proof source binding')
 cases.push({budget:r.ms,conditional:true,proven:r.proven,checked:r.checked,countedUnits:r.countedMs,wallMs:r.wallMs,checks:r.checks,replayGoals:replays.map(p=>p.goal),archiveSha256:captures[0].sha256,fileSha256:Object.fromEntries(names.map(n=>[n,sha(files[n]!)])),exactFreshFamily:true})
}
if(cases.length!==2||cases[0].budget!==2700||cases[1].budget!==6000)throw Error('conditional case roster')
const originals=[1,2,3].map(n=>{const found=rows(`original-r${n}`).filter(r=>r.id==='mldr');if(found.length!==1)throw Error('original row');return{repeat:n,...found[0].search,placement:collection.rows.find((r:any)=>r.name===`original-r${n}`).placement}})
const result={batch:collection.batch,candidate:generation[0].revision,conditionalOnly:true,finalGateGreen:false,generation:{queries:0,laws:34,archiveSha256:generation[0].sha256,familySha256:sha(generated)},conditional:cases,originals,focusedTests:tests,sourceChecksClean:true,collectionArchiveSha256:collection.logArchiveSha256}
writeFileSync(`${dir}/verified-results.json`,JSON.stringify(result,null,2)+'\n')
console.log(JSON.stringify({candidate:result.candidate,conditional:cases.map(c=>({budget:c.budget,units:c.countedUnits,checked:c.checked,exactFreshFamily:c.exactFreshFamily})),originals:originals.map(r=>({repeat:r.repeat,verdict:r.verdict,ms:r.ms})),tests:tests.passingTests,assertions:tests.assertions,complete:true}))
