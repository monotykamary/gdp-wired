import {readFileSync, writeFileSync, mkdirSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {join} from 'node:path'
const [file,out]=process.argv.slice(2) as [string,string]
const encoded=readFileSync(file,'utf8').split('\n').find(l=>l.startsWith('SHARED64 '))?.slice(9)
if(!encoded)throw Error('No complete emitted certificate in log')
const bytes=Buffer.from(encoded,'base64'), decoded=gunzipSync(bytes)
const pack=JSON.parse(decoded.toString())
if(!pack.goal||!pack.tree||!pack.lemmas?.length)throw Error('Missing certificate fields')
mkdirSync(out,{recursive:true});writeFileSync(join(out,'certificate.json.gz'),bytes)
const receipt={sha256:createHash('sha256').update(bytes).digest('hex'),jsonSha256:createHash('sha256').update(decoded).digest('hex'),bytes:bytes.length,jsonBytes:decoded.length,stats:pack.stats}
writeFileSync(join(out,'receipt.json'),JSON.stringify(receipt,null,2)+'\n');console.log(JSON.stringify(receipt))
