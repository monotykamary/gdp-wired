// A fresh process per proof: neither proof caches nor warmed global meters may hide
// a wall-dependent query allocation. Run on one isolated VM for a fixed input.
import {expect, test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {fileURLToPath} from 'node:url'

const root = fileURLToPath(new URL('../../../', import.meta.url))

test('no-lost-keys has identical counted work in ten fresh processes', () => {
  const counts: {work: number, full: number}[] = []
  for (let run = 1; run <= 10; run++) {
    const child = spawnSync(process.execPath, ['research/protocols/ic3syn/run.ts', '--only', 'sharded_kv_no_lost_keys', '--skip', 'broken', '--ms', '60000'],
      {cwd: root, encoding: 'utf8', timeout: 90_000, maxBuffer: 8 * 1024 * 1024})
    expect(child.error, `run ${run}: ${child.stderr}`).toBeUndefined()
    expect(child.status, `run ${run}: ${child.stderr}`).toBe(0)
    const row = JSON.parse(child.stdout.trim()) as {error?: string, search: {verdict: string, work: number, full: number, ms: number}}
    expect(row.error).toBeUndefined()
    expect(row.search.verdict).toBe('proven')
    const {work, full, ms} = row.search
    expect(Number.isSafeInteger(work) && work > 0).toBe(true)
    expect(Number.isSafeInteger(full) && full > 0).toBe(true)
    counts.push({work, full})
    console.log(JSON.stringify({run, work, full, ms}))
  }
  expect(new Set(counts.map(c => c.work)).size).toBe(1)
  expect(new Set(counts.map(c => c.full)).size).toBe(1)
}, 950_000)
