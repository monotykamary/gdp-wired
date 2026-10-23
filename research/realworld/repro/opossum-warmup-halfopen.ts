// Repro for circuit breaker/opossum/CircuitBreaker: with allowWarmUp, a breaker that goes half-open during the warm-up
// (opened by open(), a health check or a restored state, then resetTimeout passing) never leaves half-open: the trial
// call's failure is ignored by fail() (circuit.js:988 `if (circuit.warmUp) return;`, before the half-open check at
// :992-997), PENDING_CLOSE is already false (:724), so every later call is rejected (:711) and no timer is armed; it
// stays so after the warm-up ends.
// Runs the original opossum 10.0.0 (tag v10.0.0, commit 6c00a87a021daae4639408e1645abb69a530a841), installed from npm
// into a temp dir. `bun research/realworld/repro/opossum-warmup-halfopen.ts`
import {execSync} from 'node:child_process'
import {mkdtempSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {createRequire} from 'node:module'

const dir = mkdtempSync(join(tmpdir(), 'opossum-'))
execSync('npm init -y >/dev/null && npm install --silent opossum@10.0.0', {cwd: dir, stdio: 'inherit'})
const CircuitBreaker = createRequire(join(dir, 'index.js'))('opossum')

const sleep = (ms: number) => new Promise(r => setTimeout(r, ms))
let up = false
const breaker = new CircuitBreaker(async () => { if (!up) throw new Error('down'); return 'ok' }, {allowWarmUp: true, rollingCountTimeout: 1000, resetTimeout: 100, timeout: false})
const show = (when: string) => console.log(`${when}: closed ${breaker.closed} open ${breaker.opened} halfOpen ${breaker.halfOpen} pendingClose ${breaker.pendingClose} warmUp ${breaker.warmUp}`)
breaker.open() // by hand, as a health check does (circuit.js:882)
show('opened during the warm-up')
await sleep(150)
show('after resetTimeout')
console.log('the trial call:', await breaker.fire().catch((e: Error) => `rejected: ${e.message}`))
show('after the trial fails')
up = true // the service is back
console.log('next call:', await breaker.fire().catch((e: Error) => `rejected: ${e.message}`))
await sleep(1000)
show('after the warm-up ends')
console.log('next call:', await breaker.fire().catch((e: Error) => `rejected: ${e.message}`))
breaker.shutdown()
