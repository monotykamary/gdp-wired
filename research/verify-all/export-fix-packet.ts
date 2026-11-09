// Re-export one exact retained accepted packet. No search, proof replacement or packet edits.
import {readFileSync,writeFileSync,mkdtempSync,readdirSync} from 'node:fs'
import {join} from 'node:path'
import {tmpdir} from 'node:os'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
const root=process.argv[2]!,id=process.argv[3]!
const sha=(s:string)=>createHash('sha256').update(s).digest('hex')
const known=JSON.parse(readFileSync('research/verify-all/paxos-lean-receipts.json','utf8')).census.otherCertificates as {id:string,packetSha256:string,leanSha256:string}[]
const expected=id==='paxos_epr'?{packetSha256:'dc0e230fab5d0081a2c9d4f56b525ef314a2e78780647d3cb2fafaf3a512f386',leanSha256:'e31b4c24e46e021c0b0187d1c2b71736530c16e47db15c18eb4d8cd77cfc15b1'}:known.find(r=>r.id===id)
if(!expected)throw Error('not in accepted packet census: '+id)
const log=readFileSync(join(root,`capture-${id}.log`),'utf8'),packed=log.match(/ARCHIVE_BEGIN\n([A-Za-z0-9+/=\r\n]+)\nARCHIVE_END/)
if(!packed)throw Error('missing retained archive')
const dir=mkdtempSync(join(tmpdir(),'lean-export-fix-'))
writeFileSync(join(dir,'original.tar.xz'),Buffer.from(packed[1]!,'base64'))
const run=(cmd:string,args:string[],timeout=180000)=>{
 const p=spawnSync(cmd,args,{encoding:'utf8',timeout,maxBuffer:128*1024*1024})
 if(p.error||p.status!==0)throw Error(JSON.stringify({cmd,args,status:p.status,error:String(p.error??''),stdout:p.stdout,stderr:p.stderr}))
 return p
}
run('tar',['-xJf',join(dir,'original.tar.xz'),'-C',dir])
const files=readdirSync(dir),packet=join(dir,files.find(f=>f.endsWith('.json')&&!f.endsWith('.result.json'))!),oldLean=join(dir,files.find(f=>f.endsWith('.lean'))!)
const raw=readFileSync(packet,'utf8'),x=JSON.parse(raw),proof=x.counted?.checked?x.counted.proof:x.good.proof
if(sha(raw)!==expected.packetSha256)throw Error('original packet identity mismatch')
// Several baseline Lean files were re-exported later, but their packet bytes never changed.
const archivedLeanSha256=sha(readFileSync(oldLean,'utf8'))
if(!x.verdict.out.proven||!x.verdict.out.checked)throw Error('not originally accepted')
const proofSha256=sha(JSON.stringify(proof)),target=join(dir,'reexport.lean')
const ex=run('bun',['research/verify-all/export-captured.ts',packet,target])
const text=readFileSync(target,'utf8'),exportMetadata=JSON.parse(ex.stdout.trim())
if(!exportMetadata.packetObjectsUnchanged||exportMetadata.retainedProofSha256!==proofSha256)throw Error('in-memory proof/capture changed during export')
if(/\bsorry\b|\badmit\b|native_decide/.test(text))throw Error('untrusted proof placeholder')
if(sha(readFileSync(packet,'utf8'))!==expected.packetSha256)throw Error('packet changed on disk')
const checked=run('bash',['research/verify-all/check-lean.sh',target],1800000)
if(/sorryAx|\berror:/.test(checked.stdout+'\n'+checked.stderr))throw Error('Lean errors or placeholder')
writeFileSync(join(dir,'lean.log'),checked.stdout+'\n'+checked.stderr)
const result={id,packetSha256:sha(raw),retainedProofSha256:proofSha256,originalLeanSha256:archivedLeanSha256,auditedPriorLeanSha256:expected.leanSha256,reexportLeanSha256:sha(text),bytes:Buffer.byteLength(text),exportExit:ex.status,leanExit:checked.status,packetUnchanged:true,packetObjectsUnchanged:true,containsAlphaBridge:text.includes('QAlpha.cmachine_sound')||text.includes('QAlpha.smachine_sound'),leanWall:checked.stderr.match(/LEAN_WALL[^\n]*/)?.[0]??null,exportMetadata}
writeFileSync(join(dir,'result.json'),JSON.stringify(result,null,2))
console.log('EXPORT_FIX_RESULT '+JSON.stringify(result))
console.log('LEAN_PROOF_DEPENDENCIES\n'+checked.stdout.split('\n').filter(s=>s.includes('depends on axioms')||s.includes('does not depend on any axioms')).join('\n'))
run('tar',['-cJf',join(dir,'generated.tar.xz'),'-C',dir,'reexport.lean','result.json','lean.log'])
console.log('EXPORT_FIX_ARCHIVE_BEGIN\n'+readFileSync(join(dir,'generated.tar.xz')).toString('base64')+'\nEXPORT_FIX_ARCHIVE_END')
