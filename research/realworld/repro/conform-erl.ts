// Conformance: express-rate-limit 8.7.1 (npm; its v8.7.1 tag is the pinned commit
// c2e30b340189e287123cf5bfd89526dd2ea07d3f), the MemoryStore it ships, against the corpus rule
// (items/ratelimit-express.ts) on the same random sequences of hits, decrements, timer ticks and resetKey calls. The
// store is the real one (its interval stopped and its clearExpired called as the `tick` request); the middleware's two
// lines around it are repeated here as written: refused when totalHits > limit (rate-limit.ts:602), and no decrement once
// `Date.now() >= resetTime.getTime()` on the resetTime object increment returned (:545-552). Date.now is stubbed.
// Compared after each call: the hit's decision for the watched key, and each key's map (current, previous, none), hit
// count and reset time.
//   bun research/realworld/repro/conform-erl.ts                       (needs npm)
import {execFileSync} from 'node:child_process'
import {mkdtempSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {memoryStore} from '../items/ratelimit-express.ts'

const dir = mkdtempSync(join(tmpdir(), 'erl-conform-'))
execFileSync('npm', ['install', '--prefix', dir, '--no-audit', '--no-fund', '--silent', 'express-rate-limit@8.7.1'], {stdio: 'inherit'})
const {MemoryStore} = await import(join(dir, 'node_modules/express-rate-limit/dist/index.mjs')) as {MemoryStore: new () => any}

const r = memoryStore(), m = r.compiled()
let seed = 5
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
let clock = 0
Date.now = () => clock
let calls = 0
for (let run = 0; run < 400; run++) {
  const ps = {limit: rand(3), windowMs: 1 + rand(5), skips: rand(4) !== 0, d: rand(3)}
  const store = new MemoryStore()
  clock = 0
  store.init({windowMs: ps.windowMs})
  clearInterval(store.interval)
  const params = r.encodeParams(ps)
  let st = m.init(params), lastTick = 0
  // Hits not yet taken back: the Client object, its resetTime object, and that Date's value at the hit.
  const pending: {key: number, client: any, date: Date, at: number}[] = []
  const trace: object[] = []
  for (let i = 0; i < 30; i++) {
    clock += rand(4)
    const key = rand(3), kind = rand(10)
    const stored = (k: number) => store.current.get(String(k)) ?? store.previous.get(String(k))
    let call: {op: string, key: number, now: number, earlier: boolean} | undefined
    let real = 'done'
    if (kind < 5) {
      call = {op: 'hit', key, now: clock, earlier: false}
      const info = await store.increment(String(key))
      real = info.totalHits > ps.limit ? 'refused' : 'let through'
      if (ps.skips) pending.push({key, client: stored(key), date: info.resetTime, at: info.resetTime.getTime()})
    } else if (kind < 7) {
      // A decrement for a pending hit whose Client is still stored (a dropped one's decrement is a no-op).
      const live = pending.filter(p => stored(p.key) === p.client)
      if (!live.length) continue
      const p = live[rand(live.length)]!
      pending.splice(pending.indexOf(p), 1)
      call = {op: 'decrement', key: p.key, now: clock, earlier: p.date.getTime() !== p.at}
      if (ps.skips && !(Date.now() >= p.date.getTime())) await store.decrement(String(p.key))
    } else if (kind < 9) {
      if (clock < lastTick + ps.windowMs) continue
      call = {op: 'tick', key, now: clock, earlier: false}
      store.clearExpired()
      lastTick = clock
    } else {
      call = {op: 'resetKey', key, now: clock, earlier: false}
      await store.resetKey(String(key))
    }
    trace.push(call)
    st = m.step(params, st, r.encodeInput(call as never))
    calls++
    const fail = (what: string) => { console.log(`divergence after ${calls} calls: ${what}\nparams ${JSON.stringify(ps)}\ntrace ${JSON.stringify(trace)}`); process.exit(1) }
    const got = r.decode(st) as Record<string, any>
    if (call.op === 'hit' && call.key === ps.d && real !== (got.okD ? 'let through' : 'refused')) fail(`hit: the code ${real}, the rule ${got.okD ? 'let through' : 'refused'}`)
    for (let k = 0; k < 3; k++) {
      const where = store.current.has(String(k)) ? 2 : store.previous.has(String(k)) ? 1 : 0
      if (where !== (st.maps.Where?.get(k) ?? 0)) fail(`key ${k}: map ${where} in the code, ${st.maps.Where?.get(k) ?? 0} in the rule`)
      if (where) {
        const c = stored(k)
        if (c.totalHits !== (st.maps.Hits?.get(k) ?? 0)) fail(`key ${k}: totalHits ${c.totalHits} in the code, ${st.maps.Hits?.get(k) ?? 0} in the rule`)
        if (c.resetTime.getTime() !== (st.maps.Reset?.get(k) ?? 0)) fail(`key ${k}: resetTime ${c.resetTime.getTime()} in the code, ${st.maps.Reset?.get(k) ?? 0} in the rule`)
      }
    }
  }
  store.shutdown()
}
console.log(`agreed on ${calls} calls (400 runs of up to 30)`)
