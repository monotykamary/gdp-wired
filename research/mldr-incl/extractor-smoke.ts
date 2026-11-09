// Frozen real receipts; malformed controls keep forged success labels so the
// test checks parent/premise binding rather than trusting those labels.
import {mkdtempSync,readFileSync,writeFileSync,rmSync,mkdirSync,cpSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {brotliCompressSync,brotliDecompressSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {spawnSync} from 'node:child_process'
const source=process.argv[2]!,dir=mkdtempSync(join(tmpdir(),'incl-extract-'))
let checks=0
try{
 const run=(root:string,ok:boolean)=>{
  const r=spawnSync('bun',['research/mldr-incl/extract-pointwise.ts',root,join(dir,'out-'+checks)],{encoding:'utf8'})
  if(ok?r.status!==0:r.status===0||!r.stderr.includes('reduced premise/parent binding mismatch'))throw Error(JSON.stringify({status:r.status,stdout:r.stdout,stderr:r.stderr}))
  checks++
 }
 run(source,true)
 for(const variant of ['conclusion','order','parent']){
  const root=join(dir,variant);mkdirSync(root);cpSync(join(source,'pointwise-tight-certificate.log'),join(root,'pointwise-tight-certificate.log'))
  const rows=readFileSync(join(source,'pointwise-guarded-certificate.log'),'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l)),p=rows.find(r=>r.artifact),v=rows.find(r=>!r.artifact&&r.sha256),bundle=JSON.parse(brotliDecompressSync(Buffer.from(p.artifact.data,'base64')).toString())
  if(variant==='conclusion')bundle.hyps[bundle.hyps.length-1]={op:'=',a:{op:'const',value:0},b:{op:'const',value:0}}
  if(variant==='order'){bundle.remainingOriginalIndices.reverse();bundle.hyps.reverse();p.remainingOriginalIndices=[...bundle.remainingOriginalIndices]}
  if(variant==='parent')bundle.parentSha256='0'.repeat(64)
  const bytes=brotliCompressSync(Buffer.from(JSON.stringify(bundle))),sha256=createHash('sha256').update(bytes).digest('hex')
  p.artifact={encoding:'br',sha256,data:bytes.toString('base64')};v.sha256=sha256
  writeFileSync(join(root,'pointwise-guarded-certificate.log'),rows.map(r=>JSON.stringify(r)).join('\n')+'\n')
  run(root,false)
 }
 console.log(JSON.stringify({checks,validAccepted:1,forgedSuccessReceiptsRejected:3,variants:['conclusion','order','parent']}))
}finally{rmSync(dir,{recursive:true,force:true})}
