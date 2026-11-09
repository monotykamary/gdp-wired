// Iteration-only formatter; authoritative merge evidence comes from Lane D.
import {readFileSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
const dir = process.argv[2]!, placement = JSON.parse(readFileSync(join(dir, 'placement.json'), 'utf8'))['filter-paired']
const rows = readFileSync(join(dir, 'filter-paired.log'), 'utf8').split('\n').filter(s => s.startsWith('{')).map(s => JSON.parse(s))
if (rows.length !== 6 || new Set(rows.map(r => `${r.targeted}:${r.repeat}`)).size !== 6) throw Error('incomplete paired repeats')
for (const r of rows) if (r.queries !== 0 || r.elapsedMs > 2000) throw Error('query or finite-wall contract failed')
const summaries = rows.map(r => ({targeted:r.targeted,repeat:r.repeat,elapsedMs:r.elapsedMs,finish:r.finish,dropped:r.dropped,costly:r.dropped.filter((d:{law:string})=>/CV at most|stored guard|canVote/.test(d.law)),survivors:r.laws.length}))
const result = {scope:'same-state, same-source finite-filter iteration only; no merge-gate claim',cpu:placement.cpu,vm:placement.vm,exclusive:placement.exclusive,setupMs:rows[0].setupMs,rows:summaries}
writeFileSync(process.argv[3]!,JSON.stringify(result,null,2)+'\n')
console.log(JSON.stringify(result,null,2))
