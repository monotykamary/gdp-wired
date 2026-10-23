// Repro: @upstash/ratelimit 2.2.0 (npm, gitHead fccd840d6e0f893f50bc677107fba4d913a414e3), fixedWindow and
// slidingWindow, the counterexamples gdp-wired's search found for "a rejected request leaves the window's remaining
// tokens spendable". The library is installed from npm into a temp dir and run as shipped (its TypeScript and its Lua
// scripts). Redis is a stand-in: `eval` runs the library's own Lua script under luajit with `redis.call` over an
// in-memory store (GET, INCRBY, PEXPIRE, HMGET, HSET), which is all these scripts call; the clock is Date.now, stubbed.
//   bun research/realworld/repro/upstash-rejected-consumes.ts       (needs npm and luajit on PATH)
import {execFileSync, spawnSync} from 'node:child_process'
import {mkdtempSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'

const dir = mkdtempSync(join(tmpdir(), 'upstash-repro-'))
execFileSync('npm', ['install', '--prefix', dir, '--no-audit', '--no-fund', '--silent', '@upstash/ratelimit@2.2.0', '@upstash/redis@1.38.2'], {stdio: 'inherit'})
const {Ratelimit} = await import(join(dir, 'node_modules/@upstash/ratelimit/dist/index.js')) as {Ratelimit: any}

type Store = Record<string, {s?: number, h?: Record<string, number>}>
const lit = (x: unknown): string => typeof x === 'number' ? String(x) : typeof x === 'string' ? JSON.stringify(x) : x === null || x === undefined ? 'nil'
  : `{${Object.entries(x as object).map(([k, v]) => `[${JSON.stringify(k)}]=${lit(v)}`).join(',')}}`
const prelude = `
local store = STORE
local function out(x) if type(x) == 'table' then local t = {} for i, v in ipairs(x) do t[i] = out(v) end return '[' .. table.concat(t, ',') .. ']' elseif x == false or x == nil then return 'null' else return string.format('%d', tonumber(x)) end end
redis = {call = function(cmd, key, ...)
  local a = {...}
  if cmd == 'GET' then local e = store[key]; if e and e.s then return tostring(e.s) end return false end
  if cmd == 'INCRBY' then store[key] = store[key] or {}; store[key].s = (store[key].s or 0) + tonumber(a[1]); return store[key].s end
  if cmd == 'PEXPIRE' then return 1 end
  if cmd == 'HMGET' then local e = store[key]; local r = {} for i, f in ipairs(a) do r[i] = (e and e.h and e.h[f]) and tostring(e.h[f]) or false end return r end
  if cmd == 'HSET' then store[key] = store[key] or {h = {}}; store[key].h = store[key].h or {}; for i = 1, #a, 2 do store[key].h[a[i]] = tonumber(a[i + 1]) end return 1 end
  error('unexpected ' .. cmd)
end}
`
function fakeRedis() {
  const store: Store = {}
  const run = (script: string, keys: string[], args: unknown[]) => {
    const body = script.replace(/^#!lua[^\n]*\n/, '')
    const src = `${prelude.replace('STORE', lit(store))}KEYS = ${lit(Object.fromEntries(keys.map((k, i) => [i + 1, k])))}\nARGV = ${lit(Object.fromEntries(args.map((a, i) => [i + 1, a === null ? '' : String(a as string | number)])))}
local KEYS2, ARGV2 = {}, {} for k, v in pairs(KEYS) do KEYS2[tonumber(k)] = v end for k, v in pairs(ARGV) do ARGV2[tonumber(k)] = v end KEYS, ARGV = KEYS2, ARGV2
local res = (function() ${body} end)()
print(out(res))
for k, e in pairs(store) do if e.s then print('S', k, string.format('%d', e.s)) end if e.h then for f, v in pairs(e.h) do print('H', k, f, string.format('%d', v)) end end end`
    const p = spawnSync('luajit', ['-'], {input: src, encoding: 'utf8'})
    if (p.status !== 0) throw new Error(p.stderr)
    const [res, ...rows] = p.stdout.trim().split('\n')
    for (const r of rows) {
      const [t, k, a, b] = r.split('\t')
      if (t === 'S') store[k!] = {...store[k!], s: Number(a)}
      else store[k!] = {...store[k!], h: {...store[k!]?.h, [a!]: Number(b)}}
    }
    return JSON.parse(res!)
  }
  return {store, evalsha: async () => { throw new Error('NOSCRIPT') }, eval: async (s: string, k: string[], a: unknown[]) => run(s, k, a)}
}

let clock = 0
Date.now = () => clock
async function scenario(name: string, limiter: unknown, steps: {now: number, rate: number}[]) {
  const redis = fakeRedis()
  const rl = new Ratelimit({redis, limiter, ephemeralCache: false, enableTelemetry: false, analytics: false, prefix: 'rl'})
  console.log(`== ${name}`)
  for (const s of steps) {
    clock = s.now
    const r = await rl.limit('id', {rate: s.rate})
    console.log(`now ${s.now} rate ${s.rate}: success ${r.success}, remaining ${r.remaining}; redis ${JSON.stringify(redis.store)}`)
  }
}
// The search's runs: params {tokens: 1, window: 3}, one request {now: 2, n: 3} (fixedWindow); {tokens: 1, window: 2},
// {now: 3, n: 3} (slidingWindow). Then a request of rate 1 that the untouched limit would admit.
await scenario('fixedWindow(1, "3 ms")', Ratelimit.fixedWindow(1, '3 ms'), [{now: 2, rate: 3}, {now: 2, rate: 1}])
await scenario('slidingWindow(1, "2 ms")', Ratelimit.slidingWindow(1, '2 ms'), [{now: 3, rate: 3}, {now: 3, rate: 1}])
// PR #156's own example, here for these two: 10 tokens, 8 used, a rate of 5 is refused and the 2 left are gone.
await scenario('fixedWindow(10, "1 s"): 8 used, then rate 5, then rate 2', Ratelimit.fixedWindow(10, '1 s'), [{now: 0, rate: 8}, {now: 1, rate: 5}, {now: 2, rate: 2}])
await scenario('slidingWindow(10, "1 s"): 8 used, then rate 5, then rate 2', Ratelimit.slidingWindow(10, '1 s'), [{now: 0, rate: 8}, {now: 1, rate: 5}, {now: 2, rate: 2}])
await scenario('tokenBucket(1, "1 s", 10) for contrast (fixed in #156): 8 used, then rate 5, then rate 2', Ratelimit.tokenBucket(1, '1 s', 10), [{now: 0, rate: 8}, {now: 1, rate: 5}, {now: 2, rate: 2}])
