import {readFileSync,writeFileSync,mkdtempSync,readdirSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {tmpdir} from 'node:os'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
const root=process.argv[2]??'evidence',dir=join(root,'export-fix-all'),read=(p:string)=>readFileSync(p,'utf8'),sha=(s:string)=>createHash('sha256').update(s).digest('hex')
const old=JSON.parse(read('research/verify-all/paxos-lean-receipts.json')).census.otherCertificates as {id:string,packetSha256:string}[]
const expected=new Map([...old.map(r=>[r.id,r.packetSha256] as const),['paxos_epr','dc0e230fab5d0081a2c9d4f56b525ef314a2e78780647d3cb2fafaf3a512f386'] as const])
const summary=read(join(dir,'summary.tsv')).trim().split('\n').map(s=>s.split('\t'))
if(summary.length!==28||summary.some(r=>r[1]!=='0'||r[3]!=='boat'))throw Error('not 28 successful boat jobs')
const rows:any[]=[]
for(const filename of readdirSync(dir).filter(f=>f.endsWith('.log')).sort()){
 const text=read(join(dir,filename)),line=text.split('\n').find(l=>l.startsWith('EXPORT_FIX_RESULT '))
 if(!line)throw Error('missing result '+filename)
 const r=JSON.parse(line.slice(18))
 if(expected.get(r.id)!==r.packetSha256||!r.packetUnchanged||r.exportExit!==0||r.leanExit!==0)throw Error('invalid packet receipt '+r.id)
 if(!summary.some(s=>s[0]==='export-'+r.id))throw Error('missing job '+r.id)
 const b=text.match(/EXPORT_FIX_ARCHIVE_BEGIN\n([A-Za-z0-9+/=\r\n]+)\nEXPORT_FIX_ARCHIVE_END/);if(!b)throw Error('missing output archive')
 const tmp=mkdtempSync(join(tmpdir(),'export-fix-receipt-'));writeFileSync(join(tmp,'out.tar.xz'),Buffer.from(b[1]!,'base64'))
 const p=spawnSync('tar',['-xJf',join(tmp,'out.tar.xz'),'-C',tmp],{encoding:'utf8',timeout:30000});if(p.status!==0)throw Error(p.stderr)
 const lean=read(join(tmp,'reexport.lean')),log=read(join(tmp,'lean.log'))
 if(JSON.stringify(JSON.parse(read(join(tmp,'result.json'))))!==JSON.stringify(r))throw Error('archive result mismatch')
 if(sha(lean)!==r.reexportLeanSha256||/\bsorry\b|\badmit\b|native_decide/.test(lean)||/sorryAx|\berror:/.test(log))throw Error('invalid generated artifact '+r.id)
 if(!log.includes("'verified_laws'"))throw Error('missing original law theorem '+r.id)
 // Re-export with the final audit guards. Require byte identity with the exact
 // artifact already checked by Lean; do not repeat an unchanged Lean workload.
 const capture=read(join(root,'capture-all',`capture-${r.id}.log`)).match(/ARCHIVE_BEGIN\n([A-Za-z0-9+/=\r\n]+)\nARCHIVE_END/)
 if(!capture)throw Error('missing original packet archive')
 const original=join(tmp,'original');mkdirSync(original)
 writeFileSync(join(tmp,'capture.tar.xz'),Buffer.from(capture[1]!,'base64'))
 const unpack=spawnSync('tar',['-xJf',join(tmp,'capture.tar.xz'),'-C',original],{encoding:'utf8',timeout:30000});if(unpack.status!==0)throw Error(unpack.stderr)
 const packet=join(original,readdirSync(original).find(f=>f.endsWith('.json')&&!f.endsWith('.result.json'))!),raw=read(packet),data=JSON.parse(raw),proof=data.counted?.checked?data.counted.proof:data.good.proof
 if(sha(raw)!==r.packetSha256||sha(JSON.stringify(proof))!==r.retainedProofSha256)throw Error('original proof identity mismatch')
 const out=join(tmp,'final.lean'),fresh=spawnSync('bun',['research/verify-all/export-captured.ts',packet,out],{encoding:'utf8',timeout:180000,maxBuffer:16*1024*1024})
 if(fresh.error||fresh.status!==0)throw Error('guarded re-export failed '+r.id+' '+fresh.stderr+' '+fresh.stdout)
 const metadata=JSON.parse(fresh.stdout.trim())
 if(sha(read(out))!==r.reexportLeanSha256||sha(read(packet))!==r.packetSha256||!metadata.packetObjectsUnchanged||metadata.retainedProofSha256!==r.retainedProofSha256)throw Error('guarded re-export is not identical '+r.id)
 rows.push({...r,exportMetadata:metadata,packetObjectsUnchanged:true,finalReexportByteIdentical:true,jobSeconds:Number(summary.find(s=>s[0]==='export-'+r.id)![2]),logSha256:sha(text),compilerLogSha256:sha(log)})
}
if(rows.length!==28||new Set(rows.map(r=>r.id)).size!==28||rows.some(r=>!expected.has(r.id)))throw Error('unexpected protocol coverage')
const sourceHashes=Object.fromEntries(['lean-kernel/emit.ts','lean-kernel/lean-terms.ts','lean-kernel/qalpha.ts','lean-kernel/QAlpha.lean','research/verify-all/export-captured.ts','research/verify-all/capture-alpha.ts'].map(p=>[p,sha(read(p))]))
const payload={baseline:'0281a7e0',passed:28,total:28,sourceHashes,summarySha256:sha(read(join(dir,'summary.tsv'))),rows}
console.log('EXPORT_FIX_RECEIPTS_BEGIN\n'+JSON.stringify(payload,null,2)+'\nEXPORT_FIX_RECEIPTS_END')
console.log('EXPORT_FIX_RECEIPTS_SHA256 '+sha(JSON.stringify(payload,null,2)))
