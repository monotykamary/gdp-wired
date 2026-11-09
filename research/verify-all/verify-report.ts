import {readFileSync,existsSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {createHash} from 'node:crypto'
const log=readFileSync(process.argv[2]!, 'utf8'), root=process.argv[3]??'evidence'
const begin='REPORT_BEGIN\n', end='\nREPORT_END', a=log.indexOf(begin), b=log.lastIndexOf(end)
if(a<0||b<a)throw Error('missing report boundaries')
const report=log.slice(a+begin.length,b)
const meta=JSON.parse(log.match(/^REPORT_META (.+)$/m)![1]!)
if(createHash('sha256').update(report).digest('hex')!==meta.sha256)throw Error('report hash mismatch')
if(meta.leanPass!==27||meta.accepted!==28||meta.replayed!==11)throw Error('unexpected final tallies: '+JSON.stringify(meta))
if(/^#+.*(?:IN PROGRESS|PENDING FINAL)/im.test(report))throw Error('unfinished report')
for(const n of [1,2,3,4,5])if(!report.includes(`## ${n}. `))throw Error('missing item '+n)
const targets=[...report.matchAll(/\]\(([^)]+)\)/g)].map(m=>m[1]!).filter(x=>!/^https?:|^#/.test(x))
for(const target of targets){const path=target.startsWith('verify-all/')?join(root,target.slice('verify-all/'.length)):resolve('runs',target);if(!existsSync(path))throw Error('missing linked evidence '+target)}
const hashes=[...report.matchAll(/^([a-f0-9]{64})  verify-all\/production\/(\S+)$/gm)]
if(hashes.length!==146)throw Error('wrong number of production log hashes '+hashes.length)
for(const m of hashes){const bytes=readFileSync(join(root,'production',m[2]!));if(createHash('sha256').update(bytes).digest('hex')!==m[1])throw Error('changed production log '+m[2]);if(!bytes.includes('7ec8b310d23fab7eb3ba452b659e7051ceefe97aea01ffa6f16d990a7bea7f33'))throw Error('missing in-job kernel hash '+m[2])}
console.log(JSON.stringify({reportVerified:true,sha256:meta.sha256,bytes:meta.bytes,linkedEvidence:targets.length,productionLogHashes:hashes.length,...meta}))
