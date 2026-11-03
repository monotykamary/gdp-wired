import {readFileSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {isDeepStrictEqual} from 'node:util'
import {cases, harness, type Row} from './run.ts'
const directory = process.argv[2]!
const rows = cases.map(c => {
  const lines = readFileSync(join(directory, c.id + '.log'), 'utf8').split('\n').filter(l => l.startsWith('UPSTREAM_RESULT '))
  if (lines.length !== 1) throw new Error(`missing or duplicate receipt: ${c.id}`)
  const row = JSON.parse(lines[0]!.slice('UPSTREAM_RESULT '.length)) as Row
  if (row.id !== c.id || !isDeepStrictEqual(row.harness, harness())) throw new Error('stale worker receipt')
  return row
})
const mutants = rows.flatMap(r => r.mutants), sides = rows.flatMap(r => [r.baseline, ...r.mutants.map(m => m.side)])
const summary = {modules: rows.length, mutants: mutants.length, detected: mutants.filter(m => m.detected).length, fullyRead: sides.filter(s => s.fullyRead).length, sides: sides.length, cleanLawsProven: rows.reduce((n, r) => n + r.baseline.claims.filter(l => l.verdict === 'proven').length, 0), cleanLawsRefuted: rows.reduce((n, r) => n + r.baseline.claims.filter(l => l.verdict === 'broken').length, 0)}
writeFileSync(process.argv[3] ?? join(import.meta.dir, 'measurement.json'), JSON.stringify({version: 1, scope: 'local mutations of pinned permissively licensed upstream callable surfaces', summary, rows}, null, 2) + '\n')
console.log(JSON.stringify(summary))
