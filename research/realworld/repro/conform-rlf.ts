// Conformance: rate-limiter-flexible 11.2.3 (npm; its v11.2.3 tag is the pinned commit
// d19a457455338b73172d47d004f402bd0b748152), RateLimiterMemory, against the corpus rule
// (items/ratelimit-flexible.ts) on the same random call sequences: each call's decision (consume let through or
// refused) and, after it, each key's record as a live record reads it (value, expiresAt; a record past expiresAt is
// what incrby treats as gone). Date.now is stubbed with the calls' `now`; the run finishes before any real timer fires.
// Prints the first divergence, or how many calls agreed.
//   bun research/realworld/repro/conform-rlf.ts                       (needs npm)
import {execFileSync} from 'node:child_process'
import {mkdtempSync} from 'node:fs'
import {createRequire} from 'node:module'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {rateLimiterMemory} from '../items/ratelimit-flexible.ts'

const dir = mkdtempSync(join(tmpdir(), 'rlf-conform-'))
execFileSync('npm', ['install', '--prefix', dir, '--no-audit', '--no-fund', '--silent', 'rate-limiter-flexible@11.2.3'], {stdio: 'inherit'})
const {RateLimiterMemory} = createRequire(join(dir, 'x.js'))('rate-limiter-flexible') as {RateLimiterMemory: new (o: object) => any}

const r = rateLimiterMemory(), m = r.compiled()
let seed = 7
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
let clock = 0
Date.now = () => clock
const ops = ['consume', 'penalty', 'reward', 'block', 'set', 'delete'] as const
let calls = 0
for (let run = 0; run < 400; run++) {
  const ps = {points: rand(4), duration: rand(3), blockDuration: rand(3), d: rand(3)}
  const lim = new RateLimiterMemory({points: ps.points, duration: ps.duration, blockDuration: ps.blockDuration})
  const params = r.encodeParams(ps)
  let st = m.init(params)
  clock = 1_000_000
  const trace: object[] = []
  for (let i = 0; i < 25; i++) {
    clock += [0, 1, 500, 999, 1000, 1001, 2500][rand(7)]!
    const call = {op: ops[rand(6)]!, key: rand(3), pts: rand(4), secs: rand(3), custom: rand(4) === 0, now: clock}
    trace.push(call)
    let real: string = 'done'
    try {
      const opts = call.custom ? {customDuration: call.secs} : {}
      if (call.op === 'consume') real = await lim.consume(call.key, call.pts, opts).then(() => 'let through', () => 'refused')
      else if (call.op === 'penalty') await lim.penalty(call.key, call.pts, opts)
      else if (call.op === 'reward') await lim.reward(call.key, call.pts, opts)
      else if (call.op === 'block') await lim.block(call.key, call.secs)
      else if (call.op === 'set') await lim.set(call.key, call.pts, call.secs)
      else await lim.delete(call.key)
    } catch (e) { real = `threw ${String(e as Error)}` }
    st = m.step(params, st, r.encodeInput(call as never))
    const flags = r.decode(st) as Record<string, any>
    const ruleSays = call.op === 'consume' ? (call.key === ps.d ? (flags.okD ? 'let through' : 'refused') : undefined) : 'done'
    calls++
    const fail = (what: string) => { console.log(`divergence after ${calls} calls: ${what}\nparams ${JSON.stringify(ps)}\ntrace ${JSON.stringify(trace)}`); process.exit(1) }
    if (ruleSays !== undefined && ruleSays !== real) fail(`call ${JSON.stringify(call)}: the code ${real}, the rule ${ruleSays}`)
    for (let k = 0; k < 3; k++) {
      const rec = lim._memoryStorage._storage.get(lim.getKey(k))
      const realLive = rec && (rec.expiresAt === null || rec.expiresAt > clock)
      const has = st.maps.Has?.get(k) ?? 0, exp = st.maps.Exp?.get(k) ?? 0
      const ruleLive = has === 1 && (exp === 0 || clock < exp)
      if (!!realLive !== ruleLive) fail(`key ${k}: live in the code ${!!realLive}, in the rule ${ruleLive}`)
      if (realLive) {
        const val = (flags.Val as Record<number, number>)[k] ?? 0
        if (rec.value !== val) fail(`key ${k}: value ${rec.value} in the code, ${val} in the rule`)
        if ((rec.expiresAt ?? 0) !== exp) fail(`key ${k}: expiresAt ${rec.expiresAt} in the code, ${exp} in the rule`)
      }
    }
  }
  for (const rec of lim._memoryStorage._storage.values()) if (rec.timeoutId) clearTimeout(rec.timeoutId)
}
console.log(`agreed on ${calls} calls (400 runs of 25)`)
