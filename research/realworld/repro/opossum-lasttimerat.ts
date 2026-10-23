// Repro for circuit breaker/opossum/CircuitBreaker: toJSON's `lastTimerAt` is the time the breaker was constructed
// (circuit.js:315-316 runs `_startTimer(this)` once, in the constructor, and the 'open' listener it returns never
// updates LAST_TIMER_AT), so a breaker restored from the state of one that opened a moment ago comes back half-open
// whenever that breaker is older than resetTimeout (circuit.js:361-368).
// Runs the original opossum 10.0.0 (tag v10.0.0, commit 6c00a87a021daae4639408e1645abb69a530a841), installed from npm
// into a temp dir. `bun research/realworld/repro/opossum-lasttimerat.ts`
import {execSync} from 'node:child_process'
import {mkdtempSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {createRequire} from 'node:module'

const dir = mkdtempSync(join(tmpdir(), 'opossum-'))
execSync('npm init -y >/dev/null && npm install --silent opossum@10.0.0', {cwd: dir, stdio: 'inherit'})
const CircuitBreaker = createRequire(join(dir, 'index.js'))('opossum')

const sleep = (ms: number) => new Promise(r => setTimeout(r, ms))
const resetTimeout = 200
const options = {resetTimeout, errorThresholdPercentage: 1, timeout: false}
const old = new CircuitBreaker(async () => { throw new Error('down') }, options)
await sleep(resetTimeout + 100) // the breaker is older than resetTimeout, still closed
await old.fire().catch(() => {})
const state = old.toJSON().state
console.log('old breaker opened just now:', old.opened, 'lastTimerAt is', Date.now() - state.lastTimerAt, 'ms ago')
const restored = new CircuitBreaker(async () => 'ok', {...options, state})
console.log('restored breaker: open', restored.opened, 'halfOpen', restored.halfOpen, '(opened 0 ms ago, resetTimeout', resetTimeout, 'ms)')
console.log('a call to the restored breaker:', await restored.fire().catch((e: Error) => `rejected: ${e.message}`))
old.shutdown(); restored.shutdown()
