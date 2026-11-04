import {readFileSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {checkDocument} from '../../interchange/check.ts'
const sha=(x:Buffer|string)=>createHash('sha256').update(x).digest('hex')
const need=(x:unknown,m:string)=>{if(!x)throw Error(m)}
const manifest=JSON.parse(readFileSync('review-input/input-manifest.json','utf8'))
for(const f of manifest.inputs)need(sha(readFileSync(f.path))===f.sha256,'input changed '+f.path)
function run(command:string,args:string[],timeout:number){const r=spawnSync(command,args,{encoding:'utf8',timeout,maxBuffer:8*1024*1024});need(!r.error&&!r.signal,`driver failure ${command}: ${r.error??r.signal}`);return {code:r.status,out:r.stdout,err:r.stderr}}
const probe=run('python3',['research/process-lifecycle/probe.py'],5000)
need(probe.code===0,'pure transition probe failed: '+probe.err)
const good=run('bun',['core/cli.ts','check','research/process-lifecycle/model.py','--json','--no-propose','--ms','2000','--cert','/tmp/astra-mac-lifecycle-certs'],25000)
const bad=run('bun',['core/cli.ts','check','research/process-lifecycle/broken.py','--json','--no-propose','--ms','2000'],12000)
let g:any,b:any
try {g=JSON.parse(good.out);b=JSON.parse(bad.out)} catch {console.log('UNPARSED_GOOD '+good.out+'\n'+good.err);console.log('UNPARSED_BAD '+bad.out+'\n'+bad.err);throw Error('non-json law output')}
const laws=g.rules.flatMap((r:any)=>r.laws), negative=b.rules.flatMap((r:any)=>r.laws)
const documents=[]
for(const law of laws){if(law.cert){const raw=readFileSync(law.cert),doc=JSON.parse(raw.toString()),result=checkDocument(doc);documents.push({file:law.cert.split('/').pop(),sha256:sha(raw),certificate:doc,check:result})}}
const inputsUnchanged=manifest.inputs.every((f:any)=>sha(readFileSync(f.path))===f.sha256)
const passed=good.code===0&&bad.code===1&&laws.length===9&&laws.every((l:any)=>l.verdict==='proven')&&negative.length===1&&negative.every((l:any)=>l.verdict==='broken'&&l.run?.length)&&documents.length===9&&documents.every(d=>d.check.accepted)&&inputsUnchanged
const report={scope:'pure serialized lifecycle model only; conditional platform premise; no actual process/signaling experiment',passed,manifestSha256:sha(readFileSync('review-input/input-manifest.json')),inputsUnchanged,goodExit:good.code,badExit:bad.code,good:g,broken:b,probe:probe.out.trim(),certificateCount:documents.length,cyclicDiagnostics:[good.err,bad.err].filter(Boolean)}
const encoded=JSON.stringify(report)
console.log('LIFECYCLE_REPORT '+encoded)
console.log('LIFECYCLE_REPORT_SHA256 '+sha(encoded+'\n'))
for(const doc of documents)console.log('LIFECYCLE_CERT '+JSON.stringify(doc))
process.exitCode=passed?0:2
