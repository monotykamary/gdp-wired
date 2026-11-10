// Re-read a retained complete stream; never rerun or regenerate its tests.
import {readFileSync,writeFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {parseShardReceipt} from './shard-receipt.ts'
const rows=readFileSync(process.argv[2]!,'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>{try{return JSON.parse(l)}catch{return {}}}).filter(r=>typeof r.shard==='string'&&typeof r.gzipBase64==='string')
if(rows.length!==1)throw Error('one full-stream receipt required')
const row=rows[0],gzip=Buffer.from(row.gzipBase64,'base64'),bytes=gunzipSync(gzip,{maxOutputLength:16*1024*1024}),sha256=createHash('sha256').update(bytes).digest('hex')
if(sha256!==row.logSha256||bytes.length!==row.logBytes)throw Error('full-stream hash or size mismatch')
const receipt={shard:row.shard,childExit:row.exit,logSha256:sha256,logBytes:bytes.length,...parseShardReceipt(bytes.toString())}
if(row.exit!==0||!receipt.complete||receipt.fail)throw Error('full stream does not prove a passing shard')
if(process.argv[3]){writeFileSync(process.argv[3]+'.log.gz',gzip);writeFileSync(process.argv[3]+'.json',JSON.stringify(receipt,null,2)+'\n')}
console.log(JSON.stringify(receipt))
