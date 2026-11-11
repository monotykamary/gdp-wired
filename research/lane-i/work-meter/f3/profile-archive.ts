import {createHash} from 'node:crypto'
import {gzipSync,gunzipSync} from 'node:zlib'
export function archiveProfile(profile:unknown){
 const bytes=Buffer.from(JSON.stringify(profile)),gzip=gzipSync(bytes)
 if(bytes.length>8*1024*1024||gzip.length>1024*1024)throw Error('profile archive limit; cannot qualify capture')
 const hash=(b:Uint8Array)=>createHash('sha256').update(b).digest('hex')
 return{sha256:hash(bytes),gzipSha256:hash(gzip),bytes:bytes.length,gzipBytes:gzip.length,data:gzip.toString('base64')}
}
export function readProfileArchive(record:ReturnType<typeof archiveProfile>){
 const hash=(b:Uint8Array)=>createHash('sha256').update(b).digest('hex'),gzip=Buffer.from(record.data,'base64')
 if(gzip.length!==record.gzipBytes||hash(gzip)!==record.gzipSha256)throw Error('profile gzip mismatch')
 const bytes=gunzipSync(gzip,{maxOutputLength:8*1024*1024})
 if(bytes.length!==record.bytes||hash(bytes)!==record.sha256)throw Error('profile content mismatch')
 return JSON.parse(bytes.toString())
}
