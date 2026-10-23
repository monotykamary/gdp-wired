// Repro: express-rate-limit 8.7.1 (npm; the pinned commit c2e30b340189e287123cf5bfd89526dd2ea07d3f is its v8.7.1 tag),
// the run gdp-wired's model gives for "a decrement never lowers a count the store has reset" and "no client window lets
// through more than limit hits beyond its own hits taken back": a request of an earlier window that fails after the
// client's window was reset is taken back from the NEW window's count, because the middleware's check
// (rate-limit.ts:545 `Date.now() >= resetTime.getTime()`) reads the Client's own Date, which MemoryStore.resetClient
// moves forward in place (memory-store.ts:174). Installed from npm into a temp dir, with express, and run on a real
// server with real time (windowMs 400 ms, limit 1, skipFailedRequests).
//   bun research/realworld/repro/express-rate-limit-decrement.ts      (needs npm)
import {execFileSync} from 'node:child_process'
import {mkdtempSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'

const dir = mkdtempSync(join(tmpdir(), 'erl-repro-'))
execFileSync('npm', ['install', '--prefix', dir, '--no-audit', '--no-fund', '--silent', 'express-rate-limit@8.7.1', 'express@5.1.0'], {stdio: 'inherit'})
const express = (await import(join(dir, 'node_modules/express/index.js'))).default as any
const {rateLimit} = await import(join(dir, 'node_modules/express-rate-limit/dist/index.mjs')) as {rateLimit: any}

const sleep = (ms: number) => new Promise(r => setTimeout(r, ms))
const t0 = Date.now(), at = () => `${String(Date.now() - t0).padStart(4)} ms`
const limiter = rateLimit({windowMs: 400, limit: 1, skipFailedRequests: true, standardHeaders: 'draft-7', legacyHeaders: false})
const app = express()
app.use(limiter)
// `slow` fails after 600 ms (a failed request is taken back); `fast` succeeds at once.
app.get('/slow', async (_req: unknown, res: any) => { await sleep(600); res.status(500).send('failed') })
app.get('/slowok', async (_req: unknown, res: any) => { await sleep(600); res.send('ok') })
app.get('/fast', (_req: unknown, res: any) => res.send('ok'))
const server = app.listen(0)
const port = (server.address() as {port: number}).port
const get = async (path: string) => { const r = await fetch(`http://127.0.0.1:${port}${path}`); return r.status }

async function scenario(slowPath: string) {
const log: string[] = []
const slow = get(slowPath).then(s => log.push(`${at()} A /slow (window 1) finished: ${s}`))
log.push(`${at()} A sent`)
await sleep(450) // window 1 (0-400 ms) has passed
log.push(`${at()} B /fast (window 2): ${await get('/fast')}`) // resets the client: window 2 counts B
await slow // A fails at ~600 ms; its decrement passes the check against the moved Date and takes B's hit back
await sleep(20)
log.push(`${at()} C /fast (window 2): ${await get('/fast')}`) // a second hit let through in window 2 (limit 1)
log.push(`${at()} D /fast (window 2): ${await get('/fast')}`)
return log
}
console.log((await scenario('/slow')).join('\n'))
await sleep(500)
// Control: the same timing, but A succeeds (not taken back): C is refused.
console.log('-- control: A succeeds')
console.log((await scenario('/slowok')).join('\n'))
server.close()
console.log('First run: window 2 (from B) let through B and C with limit 1, and no request of window 2 failed: A, of window 1, was taken back from it.')
