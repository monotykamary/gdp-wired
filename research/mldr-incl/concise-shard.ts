// Capture the complete child stream before emitting a bounded summary receipt.
import {spawnSync} from 'node:child_process'
import {mkdtempSync,openSync,closeSync,readFileSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {gzipSync} from 'node:zlib'
import {parseShardReceipt} from './shard-receipt.ts'
const shard=process.argv[2]
if(!shard||!/^\d+\/\d+$/.test(shard))throw Error('shard i/N required')
const dir=mkdtempSync(join(tmpdir(),'incl-shard-')),file=join(dir,'full.log'),fd=openSync(file,'w')
try{
 const result=spawnSync('bun',['scripts/test-shards.ts','--shard',shard],{stdio:['ignore',fd,fd]})
 closeSync(fd)
 const bytes=readFileSync(file),text=bytes.toString(),gzip=gzipSync(bytes),{pass,fail,skip,runs,complete}=parseShardReceipt(text)
 console.log(JSON.stringify({shard,exit:result.status,signal:result.signal,complete,pass,fail,skip,runs,logSha256:createHash('sha256').update(bytes).digest('hex'),logBytes:bytes.length,archiveIncluded:gzip.length<98304,...(gzip.length<98304?{gzipBase64:gzip.toString('base64')}:{})}))
 if(result.status!==0||!complete||fail){console.error(text.slice(-12000));process.exitCode=1}
}finally{rmSync(dir,{recursive:true,force:true})}
