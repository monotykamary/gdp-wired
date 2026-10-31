// The Go front end's outputs before and after a change, compared byte for byte: each extraction's rule source, notes
// and refusals (in the order the test file and research/extract/go-run.ts make them).
//
//   python3 supercomputer/run.py --backend modal --jobs research/langs/go-snapshot.json --out runs/langs/go-snap-after
//   bun research/langs/go-snapshot/compare.ts runs/langs/go-snap-after
import {readFileSync} from 'node:fs'
import {join} from 'node:path'

const after = process.argv[2]
if (!after) throw new Error('compare.ts <run dir of the snapshot jobs>')
let differ = 0, same = 0
for (const j of ['tests', 'realworld']) {
  const before = readFileSync(join(import.meta.dir, `before-${j}.jsonl`), 'utf8').trim().split('\n')
  const log = readFileSync(join(after, `go-snap-${j}.log`), 'utf8')
  const now = log.slice(log.indexOf('--- snapshot') + 13).split('\n').filter(l => l.startsWith('{'))
  if (now.length !== before.length) console.log(`${j}: ${now.length} extractions against ${before.length}`)
  for (let i = 0; i < Math.max(now.length, before.length); i++) {
    if (before[i] === now[i]) { same++; continue }
    differ++
    const a = JSON.parse(before[i] ?? '{}'), b = JSON.parse(now[i] ?? '{}')
    console.log(`\n${j} #${i} ${a.entry ?? b.entry}:`)
    for (const k of ['source', 'notes', 'refusals', 'ok']) if (JSON.stringify(a[k]) !== JSON.stringify(b[k])) console.log(`  ${k}:\n    before ${JSON.stringify(a[k]).slice(0, 400)}\n    after  ${JSON.stringify(b[k]).slice(0, 400)}`)
  }
}
console.log(`\n${same} the same, ${differ} differ`)
process.exit(differ ? 1 : 0)
