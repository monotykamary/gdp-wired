// Local receipt formatting only; not a final-gate validator.
import {readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
const dir = process.argv[2]!, rows = []
for (const file of readdirSync(dir).filter(f => /-pair-\d+\.log$/.test(f)).sort()) {
 const text = readFileSync(join(dir, file), 'utf8'), start = text.indexOf('PAIR begin side=candidate')
 if (start < 0) continue
 const end = text.indexOf('PAIR end side=candidate', start), complete = end >= start
 const part = text.slice(start, complete ? end + 'PAIR end side=candidate'.length : undefined), result = part.split('\n').find(s => s.startsWith('{"id":'))
 const attempts = [...part.matchAll(/^counts: try (.*?) \| ls (\d+) pass ([01]) ms ([\d.-]+) took ([\d.-]+) wall ([\d.-]+) \[(.*?)\] -> (\S+)$/gm)].map(m => ({law:m[1]!, family:Number(m[2]), pass:Number(m[3]), share:Number(m[4]), took:Number(m[5]), wallMs:Number(m[6]), outcome:m[8]}))
 const encoded = part.match(/^T14_CAPTURE_GZIP_BASE64 (.+)$/m)?.[1]
 const capture = encoded ? JSON.parse(gunzipSync(Buffer.from(encoded, 'base64')).toString()) : undefined
 const checks: {law:string,pass:number,genuine:boolean,reason?:string}[] = capture?.modelChecks ?? []
 const genuine = checks.filter(c=>c.genuine), uncertain = checks.filter(c=>!c.genuine)
 const row = {file, complete, wall:Number(part.match(/STRICT_PROCESS_SECONDS candidate ([\d.]+)/)?.[1]), result:result?JSON.parse(result):undefined, generation:part.match(/^counts: candidates .*$/m)?.[0], rounds:[...part.matchAll(/^counts: round .*$/gm)].map(m=>m[0]), attempts:attempts.length, maxRatio:Math.max(0,...attempts.filter(a=>a.share>0).map(a=>a.took/a.share)), overrun:attempts.filter(a=>a.share>0&&a.took/a.share>1.1), total:attempts.reduce((n,a)=>n+a.took,0), targeted:attempts.filter(a=>/stored guard|canVote|one primary per term/.test(a.law)), models:{genuine,uncertain}, finite:[...part.matchAll(/^counts: finite .*$/gm)].map(m=>m[0])}
 rows.push(row)
 console.log(JSON.stringify({file,complete,wall:row.wall,attempts:row.attempts,maxRatio:row.maxRatio,overrun:row.overrun,total:row.total,rounds:row.rounds,initialFamily:attempts[0]?.family,models:{genuine:genuine.length,uncertain:uncertain.length},last:attempts.at(-1)}))
}
writeFileSync(process.argv[3]!, JSON.stringify(rows,null,2)+'\n')
