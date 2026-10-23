// Conformance for circuit breaker/cockatiel/ConsecutiveBreaker: the original cockatiel 3.2.1 (tag v3.2.1, commit
// 32a70686ef3470f6c94c1325fbc7982d582b8432, installed from npm into a temp dir) and the rule (compiled) on the same
// random request sequences: calls started, calls and tests answered (ok, a handled failure, an error the policy doesn't
// handle), isolate and dispose, time moving on (Date.now mocked). After each request the state, the breaker's count and
// (while Open) openedAt and attemptNo from toJSON() are compared; the first divergence is reported.
// A call started while HalfOpen awaits the test and calls execute() again (the rule's 'async' gap): none is sent then.
// `bun research/realworld/repro/conform-cockatiel.ts [runs]`
import {execSync} from 'node:child_process'
import {mkdtempSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {cockatiel} from '../items/queuebreaker-breaker.ts'

const dir = mkdtempSync(join(tmpdir(), 'cockatiel-'))
execSync('npm init -y >/dev/null && npm install --silent cockatiel@3.2.1', {cwd: dir, stdio: 'inherit'})
const {circuitBreaker, handleWhen, ConsecutiveBreaker, CircuitState} = await import(join(dir, 'node_modules/cockatiel/dist/index.js'))

let clock = 1000
Date.now = () => clock
const flush = () => new Promise(r => setTimeout(r, 0))
let seed = 7
const rand = (n: number) => { seed = (seed * 1103515245 + 12345) % 2147483648; return Math.floor(seed / 65536) % n }

const r = cockatiel(), x = r.compiled()
type Pending = {kind: 'closedDone' | 'testDone', resolve: (v: string) => void, reject: (e: Error) => void}
const runs = Number(process.argv[2] ?? 300)
let checked = 0
const seen: Record<string, number> = {}
for (let run = 0; run < runs; run++) {
  const threshold = 1 + rand(3), halfOpenAfter = rand(3) * 10
  const breaker = new ConsecutiveBreaker(threshold)
  const policy = circuitBreaker(handleWhen((e: Error & {unhandled?: boolean}) => !e.unhandled), {halfOpenAfter, breaker})
  const p = r.encodeParams({threshold, halfOpenAfter})
  let st = x.init(p)
  const pending: Pending[] = [], handles: {dispose(): void, done: boolean}[] = []
  const trace: string[] = []
  for (let step = 0; step < 30; step++) {
    const pick = rand(10)
    let req: Record<string, unknown> | undefined
    if (pick < 3) {
      if (policy.state === CircuitState.HalfOpen) continue
      const before = policy.state
      policy.execute(() => new Promise<string>((resolve, reject) => { pending.push({kind: before === CircuitState.Closed ? 'closedDone' : 'testDone', resolve, reject}) })).catch(() => {})
      req = {op: 'execute', outcome: 'ok', now: clock}
    } else if (pick < 6 && pending.length) {
      const k = rand(pending.length), c = pending.splice(k, 1)[0]!, outcome = (['ok', 'handled', 'unhandled'] as const)[rand(3)]!
      if (outcome === 'ok') c.resolve('ok')
      else c.reject(Object.assign(new Error(outcome), {unhandled: outcome === 'unhandled'}))
      req = {op: c.kind, outcome, now: clock}
    } else if (pick === 6 && rand(5) === 0) {
      const h = policy.isolate(); handles.push({dispose: () => h.dispose(), done: false})
      req = {op: 'isolate', outcome: 'ok', now: clock}
    } else if (pick >= 6 && pick <= 7 && handles.some(h => !h.done)) {
      const open = handles.filter(h => !h.done), h = open[rand(open.length)]!
      h.dispose(); h.done = true
      req = {op: 'dispose', outcome: 'ok', now: clock}
    } else {
      clock += rand(25)
      continue
    }
    await flush()
    trace.push(JSON.stringify(req))
    st = x.step(p, st, r.encodeInput(req as never))
    const d = r.decode(st) as {st: string, failures: number, openedAt: number, attemptNo: number}
    const own = (policy.toJSON() as {ownState: {value: number, openedAt?: number, attemptNo?: number}}).ownState
    const real = {st: CircuitState[policy.state] as string, failures: breaker.state as number, ...(policy.state === CircuitState.Open ? {openedAt: own.openedAt, attemptNo: own.attemptNo} : {})}
    const mine = {st: d.st, failures: d.failures, ...(d.st === 'Open' ? {openedAt: d.openedAt, attemptNo: d.attemptNo} : {})}
    if (JSON.stringify(real) !== JSON.stringify(mine)) {
      console.log(`divergence in run ${run} (threshold ${threshold}, halfOpenAfter ${halfOpenAfter}) after:\n  ${trace.join('\n  ')}\ncockatiel: ${JSON.stringify(real)}\nrule:      ${JSON.stringify(mine)}`)
      process.exit(1)
    }
    checked++
    seen[d.st] = (seen[d.st] ?? 0) + 1
  }
  for (const c of pending) c.resolve('ok')
  await flush()
}
console.log(`no divergence: ${runs} runs, ${checked} requests compared, states after them: ${JSON.stringify(seen)}`)
