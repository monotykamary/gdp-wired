// Conformance harness for auth/lucia/validateSession: runs Lucia's own session core (lucia@3.2.2 from npm, the release
// of the pinned v3 branch, installed into a temp dir; never vendored) over an in-memory adapter, and the rule's
// interpreter, on the same random request sequences (Date.now() pinned to each request's `now`), and reports the first
// divergence in any session's existence, user or expiry, or in what validateSession returned.
//   bun research/realworld/repro/conform-lucia.ts [dir with node_modules/lucia]
import {execSync} from 'node:child_process'
import {existsSync, mkdtempSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {lucia} from '../items/authz-lucia.ts'

let dir = process.argv[2]
if (!dir || !existsSync(join(dir, 'node_modules/lucia'))) {
  dir = mkdtempSync(join(tmpdir(), 'lucia-'))
  execSync('npm init -y && npm install lucia@3.2.2 --no-audit --no-fund', {cwd: dir, stdio: 'ignore'})
}
// @ts-expect-error lucia is installed into a temp dir at run time, not in the repo's node_modules
const {Lucia, TimeSpan} = await import(join(dir, 'node_modules/lucia/dist/index.js')) as typeof import('lucia')

type Row = {id: string, userId: string, expiresAt: Date, attributes: object}
let clock = 0
Date.now = () => clock
const rows = new Map<string, Row>()
let userExists = true
// The adapter (database.ts:7-17), in memory; the users table is one flag per call (the rule's `userExists`).
const adapter = {
  getSessionAndUser: async (id: string) => { const s = rows.get(id); return [s ? {...s} : null, s && userExists ? {id: s.userId, attributes: {}} : null] as const },
  getUserSessions: async (u: string) => [...rows.values()].filter(s => s.userId === u),
  setSession: async (s: Row) => { rows.set(s.id, {...s}) },
  updateSessionExpiration: async (id: string, d: Date) => { const s = rows.get(id); if (s) s.expiresAt = d },
  deleteSession: async (id: string) => { rows.delete(id) },
  deleteUserSessions: async (u: string) => { for (const [id, s] of rows) if (s.userId === u) rows.delete(id) },
  deleteExpiredSessions: async () => {},
}

const r = lucia(), run = r.interpreter()
let seed = 11
const rand = (n: number) => ((seed = (seed * 1103515245 + 12345) % 2 ** 31), seed % n)
const ops = ['create', 'validate', 'invalidate', 'invalidateUser'] as const
let failure: string | undefined, runs = 0
for (; runs < 2000 && !failure; runs++) {
  const E = rand(4) === 0 ? 1 + rand(3) : 1 + rand(40)
  const auth = new Lucia(adapter as never, {sessionExpiresIn: new TimeSpan(E, 'ms')})
  rows.clear()
  const ids: string[] = []
  const params = r.encodeParams({E})
  let st = run.init(params), now = rand(5)
  const trace: unknown[] = []
  for (let k = 0; k < 1 + rand(14) && !failure; k++) {
    now += rand(3) === 0 ? 0 : rand(E + 3)
    const req = {op: ops[rand(4)]!, sid: rand(ids.length + 2), user: rand(3), now, userExists: rand(5) !== 0}
    trace.push(req)
    clock = now
    userExists = req.userExists
    let got: {valid: boolean, fresh: boolean} | undefined
    if (req.op === 'create') ids.push((await auth.createSession(String(req.user), {})).id)
    else if (req.op === 'validate') { const v = await auth.validateSession(ids[req.sid] ?? `none${req.sid}`); got = {valid: v.session !== null, fresh: v.session?.fresh ?? false} }
    else if (req.op === 'invalidate') await auth.invalidateSession(ids[req.sid] ?? `none${req.sid}`)
    else await auth.invalidateUserSessions(String(req.user))
    st = run.step(params, st, r.encodeInput(req))
    const m = r.decode(st) as {valid: boolean, fresh: boolean, Sess: Record<string, {live: boolean, user: number, exp: number}>}
    const diffs: string[] = []
    if (got && (got.valid !== m.valid || got.fresh !== m.fresh)) diffs.push(`validate returned ${JSON.stringify(got)}, rule ${JSON.stringify({valid: m.valid, fresh: m.fresh})}`)
    ids.forEach((id, n) => {
      const o = rows.get(id), s = m.Sess[n] ?? {live: false, user: 0, exp: 0}
      if (Boolean(o) !== s.live) diffs.push(`session ${n}: original ${o ? 'exists' : 'gone'}, rule ${s.live ? 'live' : 'gone'}`)
      else if (o && (Number(o.userId) !== s.user || o.expiresAt.getTime() !== s.exp)) diffs.push(`session ${n}: original user ${o.userId} exp ${o.expiresAt.getTime()}, rule user ${s.user} exp ${s.exp}`)
    })
    if (diffs.length) failure = `E ${E}, after ${JSON.stringify(trace)}: ${diffs.join('; ')}`
  }
}
console.log(failure ? `DIVERGES ${failure}` : `conforms: ${runs} random runs, every session and every validateSession result equal after every request`)
