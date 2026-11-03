import {expect, test} from 'bun:test'
import {existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {acquireBarSlot, BAR_SLOT_COUNT, tryBarSlot} from './bar-slots.ts'

const scratch = resolve(import.meta.dir, '../runs/bar-test-tmp')
const temp = () => { mkdirSync(scratch, {recursive: true}); return mkdtempSync(join(scratch, 'case-')) }
const modulePath = join(import.meta.dir, 'bar-slots.ts')
const bar = join(import.meta.dir, 'bar.ts'), driver = join(import.meta.dir, 'boat-pass.py')
const start = (cmd: string[], cwd: string, env: Record<string, string | undefined> = process.env) => Bun.spawn(cmd, {cwd, env, stdin: 'ignore', stdout: 'pipe', stderr: 'pipe'})
type Child = ReturnType<typeof start>
const result = async (p: Child) => { const [code, out, err] = await Promise.all([p.exited, new Response(p.stdout).text(), new Response(p.stderr).text()]); return {code, out, err} }
const stop = async (p: Child) => { if (p.exitCode === null) { try { p.kill('SIGKILL') } catch { /* already gone */ } } await p.exited }
async function until(p: Child, word: string) {
  const reader = p.stdout.getReader()
  let timer: ReturnType<typeof setTimeout> | undefined
  try {
    await Promise.race([(async () => {
      let text = ''
      while (!text.includes(word)) { const r = await reader.read(); if (r.done) throw Error(`child exited before ${word}: ${text}`); text += new TextDecoder().decode(r.value) }
    })(), new Promise<never>((_, reject) => { timer = setTimeout(() => reject(Error(`waiting for ${word}`)), 10_000) })])
  } finally { clearTimeout(timer); reader.releaseLock() }
}

test('two slots, idempotent release, and stale metadata cannot strand a slot', () => {
  const dir = temp()
  try {
    expect(BAR_SLOT_COUNT).toBe(2)
    writeFileSync(join(dir, '0.lock'), JSON.stringify({pid: process.pid}))
    const a = tryBarSlot(dir)!, b = tryBarSlot(dir)!
    try {
      expect(a.stalePid).toBe(process.pid) // PID reuse/alive PID is not evidence of a held kernel lock.
      expect([a.slot, b.slot]).toEqual([0, 1])
      expect(tryBarSlot(dir)).toBeUndefined()
      a.release(); a.release()
      const c = tryBarSlot(dir)!
      expect(c.slot).toBe(0); c.release()
    } finally { a.release(); b.release() }
    expect(readFileSync(join(dir, '0.lock'), 'utf8')).toBe('')
    expect(existsSync(join(dir, '1.lock'))).toBe(true) // never unlink a possibly-open lock inode
  } finally { rmSync(dir, {recursive: true, force: true}) }
})

test('waiting is reported and abort does not consume or release another owner slot', async () => {
  const dir = temp(), a = tryBarSlot(dir)!, b = tryBarSlot(dir)!, messages: string[] = []
  try {
    const controller = new AbortController()
    const waiting = acquireBarSlot({dir, pollMs: 10, signal: controller.signal, log: m => messages.push(m)})
    controller.abort(Error('cancelled'))
    expect(await waiting.catch((e: unknown) => e)).toEqual(Error('cancelled'))
    expect(messages.some(m => m.includes('waiting'))).toBe(true)
    expect(tryBarSlot(dir)).toBeUndefined()
    a.release()
    const next = await acquireBarSlot({dir, pollMs: 10}); next.release()
  } finally { a.release(); b.release(); rmSync(dir, {recursive: true, force: true}) }
})

test('different worktrees and racing processes never admit more than two bars', async () => {
  const dir = temp(), journal = join(dir, 'journal'), children: Child[] = []
  try {
    for (let i = 0; i < 6; i++) {
      const cwd = join(dir, `worktree-${i}`); mkdirSync(cwd)
      children.push(start([process.execPath, '-e', `
        import {acquireBarSlot} from ${JSON.stringify(modulePath)};
        import {appendFileSync} from 'node:fs';
        const s=await acquireBarSlot({dir:${JSON.stringify(join(dir, 'slots'))},pollMs:5});
        try { appendFileSync(${JSON.stringify(journal)},'+'+process.pid+'\\n'); await Bun.sleep(100); }
        finally { appendFileSync(${JSON.stringify(journal)},'-'+process.pid+'\\n'); s.release(); }
      `], cwd))
    }
    for (const r of await Promise.all(children.map(result))) expect(r, r.err).toMatchObject({code: 0})
    let active = 0, entered = 0
    for (const line of readFileSync(journal, 'utf8').trim().split('\n')) {
      active += line.startsWith('+') ? 1 : -1
      if (line.startsWith('+')) entered++
      expect(active).toBeGreaterThanOrEqual(0); expect(active).toBeLessThanOrEqual(2)
    }
    expect(entered).toBe(6); expect(active).toBe(0)
  } finally { await Promise.all(children.map(stop)); rmSync(dir, {recursive: true, force: true}) }
}, 30_000)

test('SIGKILL releases the kernel lock and the next owner clears stale PID metadata', async () => {
  const dir = temp(), a = tryBarSlot(dir)!
  const child = start([process.execPath, '-e', `
    import {acquireBarSlot} from ${JSON.stringify(modulePath)};
    await acquireBarSlot({dir:${JSON.stringify(dir)}});
    console.log('ready'); setInterval(()=>{},1000);
  `], dir)
  try {
    await until(child, 'ready')
    expect(tryBarSlot(dir)).toBeUndefined()
    await stop(child)
    const reclaimed = tryBarSlot(dir)!
    expect(reclaimed.slot).toBe(1); expect(reclaimed.stalePid).toBe(child.pid)
    reclaimed.release()
  } finally { await stop(child); a.release(); rmSync(dir, {recursive: true, force: true}) }
}, 30_000)

test('quick-bar CLI waits before demand, read-only CLI bypasses slots, and exits release ownership', async () => {
  const home = temp(), dir = join(home, '.local/share/gdp-wired/bar-slots'), bin = join(home, 'bin'), calls = join(home, 'drivers')
  mkdirSync(bin)
  writeFileSync(join(bin, 'git'), `#!/bin/sh\nprintf '%s\\n' '${home}/repo/.git'\n`, {mode: 0o755})
  writeFileSync(join(bin, 'python3'), `#!/bin/sh\necho called >> '${calls}'\n`, {mode: 0o755})
  writeFileSync(join(bin, 'sh'), '#!/bin/sh\nexit 0\n', {mode: 0o755}) // never run real pool cleanup in this test
  const env = {...process.env, HOME: home, PATH: `${bin}:${process.env.PATH}`, GDPW_BAR_DIR: join(home, 'bar')}
  const a = tryBarSlot(dir)!, b = tryBarSlot(dir)!, children: Child[] = []
  try {
    const read = start([process.execPath, bar, 'failed', join(home, 'absent')], home, env); children.push(read)
    expect(await result(read)).toMatchObject({code: 0})
    expect(existsSync(calls)).toBe(false)
    const waiting = start([process.execPath, bar, '--quick', '--only', 'not-a-group'], home, env); children.push(waiting)
    await until(waiting, 'waiting for one of 2')
    expect(waiting.exitCode).toBeNull(); expect(existsSync(calls)).toBe(false)
    waiting.kill('SIGTERM'); expect(await waiting.exited).toBe(130)
    expect(tryBarSlot(dir)).toBeUndefined()
    a.release()
    const invalid = start([process.execPath, bar, '--quick', '--only', 'not-a-group'], home, env); children.push(invalid)
    expect(await result(invalid)).toMatchObject({code: 1})
    expect(existsSync(calls)).toBe(true)
    const freed = tryBarSlot(dir)!
    expect(freed.slot).toBe(0); freed.release()
  } finally { await Promise.all(children.map(stop)); a.release(); b.release(); rmSync(home, {recursive: true, force: true}) }
}, 30_000)

test('one explicit-boat driver preserves arguments without importing or re-execing Modal', async () => {
  const dir = temp(), door = join(dir, 'supercomputer'), runners = join(dir, 'compare')
  mkdirSync(door); mkdirSync(runners)
  writeFileSync(join(door, 'agent.py'), "import types\ndef modal_stub():\n    m=types.ModuleType('modal')\n    m.stub=True\n    return m\n")
  writeFileSync(join(door, 'fanout.py'), "def reexec_with_modal():\n    raise AssertionError('must not re-exec')\ndef cli(run):\n    reexec_with_modal()\n    run()\n")
  writeFileSync(join(runners, 'modal.py'), "raise AssertionError('must not import the real client')\n")
  const runner = join(runners, 'run.py')
  writeFileSync(runner, "import modal, fanout, json, sys, os\nassert modal.stub\ndef run():\n    print(json.dumps({'args':sys.argv[1:],'pid':os.getpid()}))\nfanout.cli(run)\n")
  const children: Child[] = []
  try {
    const args = ['--backend', 'boat', '--only', 'a|b', '--out', 'a path']
    const p = start(['python3', driver, dir, runner, ...args], dir); children.push(p)
    const r = await result(p)
    expect(r, r.err).toMatchObject({code: 0})
    expect(JSON.parse(r.out)).toEqual({args, pid: p.pid})
    const invalid = start(['python3', driver, dir, runner, '--backend', 'auto'], dir); children.push(invalid)
    const bad = await result(invalid)
    expect(bad.code).toBe(1); expect(bad.err).toContain('explicit --backend boat')
  } finally { await Promise.all(children.map(stop)); rmSync(dir, {recursive: true, force: true}) }
})
