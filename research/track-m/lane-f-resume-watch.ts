// Observe already-admitted Lane F batches after their original clients timed out.
// Never submits, closes or cancels work. One bounded long-poll waiter per batch.
import {mkdirSync, readFileSync, writeFileSync} from 'node:fs'
import {homedir} from 'node:os'
import {join} from 'node:path'

type Row = {name: string, code?: number, seconds?: number, vm?: string, run_name?: string, [key: string]: unknown}
type Poll = {rows?: Row[], done?: boolean, err?: string, recovering?: boolean}
const batches = [
  {id: '20261110-000831-t0pk2d', out: 'runs/lane-f-triangle-source-v2', expected: ['closure']},
  {id: '20261110-000828-1phcme', out: 'runs/lane-f-initial-transport-v2', expected: ['original34-0', 'original34-1']},
  {id: '20261110-000834-wjnlsd', out: 'runs/lane-f-commitlint-v2', expected: ['commitlint']},
]
const port = Number(process.env.SUPERCOMPUTER_SCHEDULER_PORT ?? 8790)
if (!Number.isInteger(port) || port < 1 || port > 65535) throw Error('invalid scheduler port')
const token = readFileSync(join(homedir(), '.local/share/supercomputer/live/scheduler/token'), 'utf8').trim()
const deadline = Date.now() + 30 * 60_000
async function request(path: '/poll' | '/snapshot' | '/logs', body: object, timeoutMs = 30_000): Promise<Response> {
  const response = await fetch(`http://127.0.0.1:${port}${path}`, {
    method: 'POST', headers: {'X-SC-Token': token, 'Content-Type': 'application/json'},
    body: JSON.stringify(body), signal: AbortSignal.timeout(timeoutMs),
  })
  if (!response.ok) throw Error(`scheduler ${path}: HTTP ${response.status}`)
  return response
}
async function observe(batch: typeof batches[number]): Promise<void> {
  mkdirSync(batch.out, {recursive: true})
  const rows: Row[] = [], names = new Set<string>()
  let since = 0, done = false
  while (!done && Date.now() < deadline) {
    const response = await request('/poll', {batch: batch.id, since, wait: 15})
    const result = await response.json() as Poll
    if (result.err) throw Error(`${batch.id}: ${result.err}`)
    if (!Array.isArray(result.rows)) throw Error(`${batch.id}: missing rows`)
    for (const row of result.rows) {
      since++
      if (!batch.expected.includes(row.name) || names.has(row.name)) throw Error(`${batch.id}: unexpected/duplicate row ${row.name}`)
      names.add(row.name); rows.push(row)
      writeFileSync(join(batch.out, 'recovered-rows.json'), JSON.stringify({batch: batch.id, rows}, null, 2) + '\n')
      console.log(JSON.stringify({batch: batch.id, name: row.name, workerCode: row.code, seconds: row.seconds, vm: row.vm}))
    }
    done = result.done === true
  }
  if (!done || rows.length !== batch.expected.length) throw Error(`${batch.id}: incomplete observation; received ${rows.length}/${batch.expected.length}`)
  const snapshot = await (await request('/snapshot', {batch: batch.id})).json()
  writeFileSync(join(batch.out, 'recovered-snapshot.json'), JSON.stringify(snapshot, null, 2) + '\n')
  const vms = [...new Set(rows.flatMap(row => row.vm ? [row.vm] : []))]
  const logs = new Uint8Array(await (await request('/logs', {batch: batch.id, vms}, 120_000)).arrayBuffer())
  writeFileSync(join(batch.out, 'recovered-logs.tar.gz'), logs)
  console.log(JSON.stringify({batch: batch.id, recovered: true, logsBytes: logs.length, allWorkerCodesZero: rows.every(row => row.code === 0)}))
}
const results = await Promise.allSettled(batches.map(observe))
for (let i = 0; i < results.length; i++) {
  const result = results[i]!
  if (result.status === 'rejected') {
    console.error(JSON.stringify({batch: batches[i]!.id, observationFailed: String(result.reason)}))
    process.exitCode = 1
  }
}
