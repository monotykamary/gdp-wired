// Repro for circuit breaker/cockatiel/ConsecutiveBreaker: a call admitted while Closed that fails after the circuit
// has gone half-open reopens it while the test is still in flight, and the next call starts a second test.
// Runs the original cockatiel 3.2.1 (tag v3.2.1, commit 32a70686ef3470f6c94c1325fbc7982d582b8432), installed from npm
// into a temp dir. `bun research/realworld/repro/cockatiel-stale-failure.ts`
import {execSync} from 'node:child_process'
import {mkdtempSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'

const dir = mkdtempSync(join(tmpdir(), 'cockatiel-'))
execSync('npm init -y >/dev/null && npm install --silent cockatiel@3.2.1', {cwd: dir, stdio: 'inherit'})
const {circuitBreaker, handleAll, ConsecutiveBreaker, CircuitState} = await import(join(dir, 'node_modules/cockatiel/dist/index.js'))

const tick = () => new Promise(r => setTimeout(r, 5))
const pending = () => { let resolve!: (v: string) => void, reject!: (e: Error) => void; const p = new Promise<string>((a, b) => { resolve = a; reject = b }); return {p, resolve, reject} }
const name = (s: number) => CircuitState[s]

// The rule's run (the search's, with threshold 1 for a plainer story): two calls while Closed, the first fails (opens),
// a call after halfOpenAfter (0) is the test, the second (stale) call fails, another call.
const policy = circuitBreaker(handleAll, {halfOpenAfter: 0, breaker: new ConsecutiveBreaker(1)})
let testsInFlight = 0
const a = pending(), b = pending()
const ra = policy.execute(() => a.p).catch(() => 'a failed')
const rb = policy.execute(() => b.p).catch(() => 'b failed')
await tick()
a.reject(new Error('a')); await ra; await tick()
console.log('after A fails:', name(policy.state))
const t1 = pending()
const rt1 = policy.execute(() => { testsInFlight++; return t1.p.finally(() => testsInFlight--) })
await tick()
console.log('after the first call past halfOpenAfter:', name(policy.state), 'tests in flight:', testsInFlight)
b.reject(new Error('b (admitted while Closed)')); await rb; await tick()
console.log('after the stale B fails:', name(policy.state), 'tests in flight:', testsInFlight)
const t2 = pending()
const rt2 = policy.execute(() => { testsInFlight++; return t2.p.finally(() => testsInFlight--) })
await tick()
console.log('after the next call:', name(policy.state), 'tests in flight:', testsInFlight)
t1.resolve('ok'); await rt1; await tick()
console.log('after the first test succeeds:', name(policy.state), 'tests in flight:', testsInFlight)
t2.resolve('ok'); await rt2
