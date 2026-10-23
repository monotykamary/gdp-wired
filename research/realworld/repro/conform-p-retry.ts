// Conformance for queue/p-retry/pRetry: the original p-retry 8.0.1 (tag v8.0.1, commit
// 81cd2f0e523faeeff685c5878224a0d7390ff0db, installed from npm into a temp dir) and the rule (compiled) on the same
// random runs: each attempt resolves or throws (an AbortError, a plain TypeError, another error), shouldConsumeRetry and
// shouldRetry answer from the script, and time moves on during the attempt and in shouldRetry (performance.now mocked;
// setTimeout mocked to move the clock by its delay and fire at once). Per attempt the wait p-retry asked for is
// compared with the rule's, and at the end the attempts and the outcome; the first divergence is reported.
// `bun research/realworld/repro/conform-p-retry.ts [runs]`
import {execSync} from 'node:child_process'
import {mkdtempSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {pRetry as rule} from '../items/queuebreaker-queue.ts'

const dir = mkdtempSync(join(tmpdir(), 'p-retry-'))
execSync('npm init -y >/dev/null && npm install --silent p-retry@8.0.1', {cwd: dir, stdio: 'inherit'})
const {default: pRetry, AbortError} = await import(join(dir, 'node_modules/p-retry/index.js'))

let clock = 0
performance.now = () => clock
let waits: number[] = []
const realSetTimeout = globalThis.setTimeout
globalThis.setTimeout = ((f: () => void, ms: number) => { waits.push(ms); clock += ms; queueMicrotask(f); return {unref() {}} }) as never
globalThis.clearTimeout = (() => {}) as never
let seed = 11
const rand = (n: number) => { seed = (seed * 1103515245 + 12345) % 2147483648; return Math.floor(seed / 65536) % n }

const r = rule(), x = r.compiled()
const runs = Number(process.argv[2] ?? 500)
let attemptsChecked = 0, waitsChecked = 0
for (let run = 0; run < runs; run++) {
  const forever = rand(6) === 0, retries = rand(5), factor = rand(4), minTimeout = rand(4) * 10
  const hasMaxTimeout = rand(2) === 1, maxTimeout = rand(60), hasMaxRetryTime = rand(2) === 1, maxRetryTime = rand(300)
  type Attempt = {ok: boolean, abort: boolean, typeError: boolean, consume: boolean, retry: boolean, dur1: number, dur2: number}
  const script: Attempt[] = Array.from({length: 12}, () => ({ok: rand(10) === 0, abort: rand(25) === 0, typeError: rand(25) === 0, consume: rand(4) !== 0, retry: rand(25) !== 0, dur1: rand(20), dur2: rand(5)}))
  clock = 0; waits = []
  const perAttempt: {now: number, wait: number}[] = []
  let k = -1
  const at = () => script[Math.min(k, script.length - 1)]!
  const outcome = await pRetry(async () => {
    if (k >= 0) perAttempt[k]!.wait = waits.reduce((a, b) => a + b, 0), waits = []
    k++
    if (k >= script.length) return 'ok'
    clock += at().dur1
    perAttempt[k] = {now: clock, wait: 0}
    if (at().ok) return 'ok'
    if (at().abort) throw new AbortError('stop')
    if (at().typeError) throw new TypeError('bad')
    throw new Error('fail')
  }, {
    retries: forever ? Infinity : retries, factor, minTimeout, maxTimeout: hasMaxTimeout ? maxTimeout : Infinity, maxRetryTime: hasMaxRetryTime ? maxRetryTime : Infinity,
    shouldConsumeRetry: () => at().consume,
    shouldRetry: () => { clock += at().dur2; perAttempt[k]!.now = clock; return at().retry },
  }).then(() => 'resolved', () => 'rejected')
  if (k >= 0 && perAttempt[k]) perAttempt[k]!.wait = waits.reduce((a, b) => a + b, 0)
  if (k >= script.length) { continue } // ran past the script: the input resolved by default; not compared
  const p = r.encodeParams({retries, forever, factor, minTimeout, hasMaxTimeout, maxTimeout, hasMaxRetryTime, maxRetryTime} as never) // (its type lists the rule's .fns too)
  let st = x.init(p)
  for (let i = 0; i <= k; i++) {
    const a = script[i]!
    st = x.step(p, st, r.encodeInput({ok: a.ok, abort: a.abort, typeError: a.typeError, consume: a.consume, retry: a.retry, now: perAttempt[i]!.now}))
    const d = r.decode(st) as {st: string, attempts: number, waited: number}
    attemptsChecked++
    if (perAttempt[i]!.wait > 0) waitsChecked++
    const realWait = perAttempt[i]!.wait, last = i === k
    if (d.waited !== realWait && !(last && d.st !== 'running')) {
      console.log(`divergence in run ${run} at attempt ${i + 1}: p-retry waited ${realWait}, the rule ${d.waited}\n params ${JSON.stringify({retries, forever, factor, minTimeout, hasMaxTimeout, maxTimeout, hasMaxRetryTime, maxRetryTime})}\n attempts ${JSON.stringify(script.slice(0, k + 1))}\n times ${JSON.stringify(perAttempt)}`)
      process.exit(1)
    }
    if (last && (d.st !== outcome || d.attempts !== k + 1)) {
      console.log(`divergence in run ${run}: p-retry ${outcome} after ${k + 1} attempts, the rule ${d.st} after ${d.attempts}\n params ${JSON.stringify({retries, forever, factor, minTimeout, hasMaxTimeout, maxTimeout, hasMaxRetryTime, maxRetryTime})}\n attempts ${JSON.stringify(script.slice(0, k + 1))}\n times ${JSON.stringify(perAttempt)}`)
      process.exit(1)
    }
  }
}
globalThis.setTimeout = realSetTimeout
console.log(`no divergence: ${runs} runs, ${attemptsChecked} attempts compared (${waitsChecked} with a wait)`)
