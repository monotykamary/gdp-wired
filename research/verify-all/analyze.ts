// Run on boat with --data runs/verify-all:evidence. Parse retained logs, never infer a verdict from job exit 0.
import {readFileSync, readdirSync, existsSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
const dir = process.argv[2] ?? 'evidence'
const sha = (s: string) => createHash('sha256').update(s).digest('hex')
const jsonLines = (s: string): any[] => s.split('\n').flatMap(l => { try {return [JSON.parse(l)]} catch {return []} })
const batches = ['production', 'duo-paired', 'replay', 'capture-all', 'capture-pilot', 'capture-retry']
const result: any = {batches: {}, files: {}}
for (const batch of batches) {
  const path = join(dir, batch)
  if (!existsSync(path)) continue
  const logs = readdirSync(path).filter(f => f.endsWith('.log')).sort()
  result.batches[batch] = logs.map(file => {
    const text = readFileSync(join(path, file), 'utf8'), js = jsonLines(text)
    result.files[`${batch}/${file}`] = sha(text)
    const row: any = {file, sha256: sha(text), bytes: text.length}
    if (batch === 'production') {
      const meta = text.match(/VERIFY suite=(\S+) id=(\S+) repeat=(\d+) mode=(\S+)/)
      if (meta) Object.assign(row, {suite: meta[1], id: meta[2], repeat: +meta[3]!, mode: meta[4]})
      row.output = js.find(x => x.id && (x.search || x.broken || x.error))
      row.exit = Number(text.match(/RESULT exit=(\d+)/)?.[1] ?? -1)
      row.wall = Number(text.match(/WALL seconds=([0-9.]+)/)?.[1] ?? NaN)
      row.kernelSha256 = text.match(/([0-9a-f]{64})  kernel\/kernel.ts/)?.[1]
      row.cpu = text.match(/Model name:\s*(.+)/)?.[1]
      row.pin = text.match(/PIN cpus=(.+)/)?.[1]
    } else if (batch === 'duo-paired') {
      row.sides = [...text.matchAll(/PAIR begin side=(\w+) id=(\S+) run=(\d+)\n([\s\S]*?)PAIR end side=\1 exit=(\d+)/g)].map(m => ({side:m[1],id:m[2],repeat:+m[3]!,exit:+m[5]!,output:jsonLines(m[4]!).find(x=>x.id)}))
    } else {
      row.harness = js.find(x => x.id && (x.search || x.broken))
      row.export = js.find(x => x.captureSha256)
      row.captureExit = Number(text.match(/CAPTURE_EXIT (\d+)/)?.[1] ?? -1)
      row.exportExit = Number(text.match(/EXPORT_EXIT (\d+)/)?.[1] ?? -1)
      row.leanExit = text.match(/LEAN_EXIT (\d+)/) ? Number(text.match(/LEAN_EXIT (\d+)/)![1]) : null
      row.axioms = text.split('\n').filter(l => l.startsWith("'verified") && l.includes('depends on axioms'))
      row.leanErrors = text.split('\n').filter(l => /error:|panicked|bad_alloc|maximum recursion/.test(l)).slice(0,10)
      row.archiveBytes = Number(text.match(/ARCHIVE_BYTES (\d+)/)?.[1] ?? 0)
    }
    return row
  })
  for(const name of ['summary.tsv','placement.json','backends.json']) if(existsSync(join(path,name))) result.files[`${batch}/${name}`] = sha(readFileSync(join(path,name),'utf8'))
}
const production = result.batches.production ?? []
result.counts = {}
for (const suite of ['ic3syn','duoai']) {
  const rows = production.filter((r:any)=>r.suite === suite && r.mode === 'search')
  result.counts[suite] = {attempts:rows.length, proven:rows.filter((r:any)=>r.exit===0 && r.output?.search?.verdict==='proven').length, refuted:rows.filter((r:any)=>r.output?.search?.verdict==='refuted').length, unknown:rows.filter((r:any)=>r.output?.search?.verdict==='unknown').length, timedOut:rows.filter((r:any)=>r.exit===137||r.exit===124).length, errors:rows.filter((r:any)=>r.output?.error).length, missing:rows.filter((r:any)=>!r.output).length}
}
const broken=production.filter((r:any)=>r.mode==='broken')
result.counts.broken={attempts:broken.length,proven:broken.filter((r:any)=>r.output?.broken?.verdict==='proven').length,refuted:broken.filter((r:any)=>r.output?.broken?.verdict==='refuted').length,unknown:broken.filter((r:any)=>r.output?.broken?.verdict==='unknown').length,timedOut:broken.filter((r:any)=>r.exit===137||r.exit===124).length}
console.log('COUNTS ' + JSON.stringify(result.counts))
for (const suite of ['ic3syn', 'duoai']) for (const id of [...new Set(production.filter((r:any)=>r.suite === suite).map((r:any)=>r.id))]) console.log('MEASURE ' + JSON.stringify({suite,id,rows:production.filter((r:any)=>r.suite===suite && r.id===id).map((r:any)=>({...r,output:r.output ? {...r.output,search:r.output.search ? {...r.output.search,foundCount:r.output.search.found?.length ?? 0,found:undefined} : undefined,broken:r.output.broken ? {...r.output.broken,foundCount:r.output.broken.found?.length ?? 0,found:undefined} : undefined} : undefined}))}))
console.log('LEDGER ' + JSON.stringify(result))
