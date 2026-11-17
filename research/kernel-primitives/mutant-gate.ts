import {spawnSync} from 'node:child_process'
import {writeFileSync} from 'node:fs'
import {resolve} from 'node:path'

const root = resolve(import.meta.dir, '../..')
const list = spawnSync('bun', ['kernel/mutants.ts', 'list'], {cwd: root, encoding: 'utf8', timeout: 20_000, maxBuffer: 4 * 1024 * 1024})
if (list.error || list.status !== 0) throw new Error(`mutant discovery failed: ${String(list.error)} ${list.stderr}`)
const ids = list.stdout.split('\n').filter(line => ['kernel/integer-primitives.ts', 'kernel/word-division.ts'].some(file => line.includes(String.fromCharCode(9) + file + ':'))).map(line => Number(line.split('\t')[0]))
if (!ids.length) throw new Error('no primitive mutants discovered')
const run = spawnSync('bun', ['kernel/mutants.ts', 'ids', ids.join(',')], {cwd: root, encoding: 'utf8',
  env: {...process.env, MUTANT_BATTERY: 'integer primitives,word division'}, timeout: 650_000, maxBuffer: 4 * 1024 * 1024})
const output = process.env.SUPERCOMPUTER_OUTPUT_DIR
if (!output) throw new Error('results-only gate requires SUPERCOMPUTER_OUTPUT_DIR')
writeFileSync(resolve(output, 'mutants.jsonl'), run.stdout)
writeFileSync(resolve(output, 'mutants.stderr'), run.stderr)
if (run.error || run.status !== 0) throw new Error(`mutant execution failed: ${String(run.error)} status=${run.status}`)
const rows = run.stdout.trim().split('\n').filter(Boolean).map(line => JSON.parse(line) as {id: number, killedBy?: string, equivalent?: string})
if (rows.length !== ids.length || new Set(rows.map(row => row.id)).size !== ids.length || rows.some(row => !ids.includes(row.id)))
  throw new Error('mutant result coverage does not match discovery')
const survivors = rows.filter(row => !row.killedBy && !row.equivalent)
const receipt = {discovered: ids.length, killed: rows.filter(row => row.killedBy).length, equivalent: rows.filter(row => !row.killedBy && row.equivalent).length, survivors: survivors.map(row => row.id)}
writeFileSync(resolve(output, 'mutation-receipt.json'), JSON.stringify(receipt) + '\n')
console.log(JSON.stringify(receipt))
if (survivors.length) process.exitCode = 1
