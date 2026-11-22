import {expect, test} from 'bun:test'
import {cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {join, resolve} from 'node:path'
import {acquireBarSlot, BAR_SLOT_COUNT, tryBarSlot} from './bar-slots.ts'

const scratch = resolve(import.meta.dir, '../runs/bar-test-tmp')
const temp = () => { mkdirSync(scratch, {recursive: true}); return mkdtempSync(join(scratch, 'case-')) }
const modulePath = join(import.meta.dir, 'bar-slots.ts')
const bar = join(import.meta.dir, 'bar.ts')
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

test('quick-bar CLI waits for a slot before any launch, read-only CLI bypasses slots, and exits release ownership', async () => {
  const home = temp(), dir = join(home, '.local/share/gdp-wired/bar-slots'), bin = join(home, 'bin'), calls = join(home, 'launches')
  mkdirSync(bin)
  writeFileSync(join(bin, 'git'), `#!/bin/sh\nprintf '%s\\n' '${home}/repo/.git'\n`, {mode: 0o755})
  writeFileSync(join(bin, 'supercomputer'), `#!/bin/sh\nprintf '%s\\n' "$*" >> '${calls}'\n`, {mode: 0o755}) // never launch real boxes in this test
  const env = {...process.env, HOME: home, PATH: `${bin}:${process.env.PATH}`, GDPW_BAR_DIR: join(home, 'bar')}
  const a = tryBarSlot(dir)!, b = tryBarSlot(dir)!, children: Child[] = []
  try {
    const read = start([process.execPath, bar, 'failed', join(home, 'absent')], home, env); children.push(read)
    expect(await result(read)).toMatchObject({code: 0})
    const waiting = start([process.execPath, bar, '--quick', '--only', 'not-a-group'], home, env); children.push(waiting)
    await until(waiting, 'waiting for one of 2')
    expect(waiting.exitCode).toBeNull()
    waiting.kill('SIGTERM'); expect(await waiting.exited).toBe(130)
    expect(tryBarSlot(dir)).toBeUndefined()
    a.release()
    const invalid = start([process.execPath, bar, '--quick', '--only', 'not-a-group'], home, env); children.push(invalid)
    const bad = await result(invalid)
    expect(bad.code).toBe(1); expect(bad.err).toContain('no group not-a-group')
    const retired = start([process.execPath, bar, '--quick', '--only', 'chc'], home, env); children.push(retired)
    const old = await result(retired)
    expect(old.code).toBe(1); expect(old.err).toContain('retired with its Modal runner')
    const freed = tryBarSlot(dir)!
    expect(freed.slot).toBe(0); freed.release()
    const gone = start([process.execPath, bar, '--backend', 'boat', '--only', 'suite'], home, env); children.push(gone)
    const flagGone = await result(gone)
    expect(flagGone.code).toBe(1); expect(flagGone.err).toContain('--backend is gone')
    expect(existsSync(calls)).toBe(false)
  } finally { await Promise.all(children.map(stop)); a.release(); b.release(); rmSync(home, {recursive: true, force: true}) }
}, 30_000)

test('dirty candidate pilots resolve a real snapshot root without changing its content key', async () => {
  const dir = temp(), src = join(dir, 'source'), bin = join(dir, 'bin'), store = join(dir, 'bar'), children: Child[] = []
  const env = {...process.env, HOME: dir, GIT_CONFIG_GLOBAL: '/dev/null', GIT_CONFIG_NOSYSTEM: '1',
    GIT_AUTHOR_NAME: 'bar test', GIT_AUTHOR_EMAIL: 'bar@example.invalid', GIT_COMMITTER_NAME: 'bar test', GIT_COMMITTER_EMAIL: 'bar@example.invalid',
    PATH: `${bin}:${process.env.PATH}`, GDPW_BAR_DIR: store}
  const git = (cwd: string, ...args: string[]) => {
    const p = Bun.spawnSync(['git', ...args], {cwd, env, stdout: 'pipe', stderr: 'pipe'})
    expect(p.exitCode, p.stderr.toString()).toBe(0)
    return p.stdout.toString().trim()
  }
  const put = (p: string, text: string) => writeFileSync(p, text)
  try {
    for (const p of [src, bin, join(src, 'gates'), join(src, 'supercomputer')]) mkdirSync(p, {recursive: true})
    writeFileSync(join(bin, 'bun'), `#!/bin/sh\nif [ "$1" = install ]; then exit 0; fi\nexec '${process.execPath}' "$@"\n`, {mode: 0o755})
    // `supercomputer run` as a pass sees it: the tree it would pack (its cwd's git root) as a receipt, every job answered 0
    const fake = join(dir, 'supercomputer.ts')
    put(fake, `import {mkdirSync, readFileSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
const a = process.argv.slice(2), at = (k: string) => a[a.indexOf(k) + 1]!
if (a[0] !== 'run') process.exit(2)
const git = (...args: string[]) => { const p = Bun.spawnSync(['git', ...args], {stdout: 'pipe', stderr: 'pipe'}); if (p.exitCode) throw Error(p.stderr.toString()); return p.stdout.toString() }
const out = at('--out'); mkdirSync(out, {recursive: true})
const root = git('rev-parse', '--show-toplevel').trim(), common = git('rev-parse', '--path-format=absolute', '--git-common-dir').trim()
const files = [...git('ls-files', '-z', '--recurse-submodules').split('\\0'), ...git('ls-files', '-z', '--others', '--exclude-standard').split('\\0')].filter(Boolean)
if (root !== process.cwd()) throw Error('wrong snapshot root: ' + root + ' from ' + process.cwd())
writeFileSync(join(out, 'root.json'), JSON.stringify({root, common, files}))
const jobs = JSON.parse(readFileSync(at('--jobs'), 'utf8')) as {name: string}[]
for (const j of jobs) writeFileSync(join(out, j.name + '.log'), 'ok\\n')
writeFileSync(join(out, 'batch.json'), JSON.stringify({id: 'fixture'}))
writeFileSync(join(out, 'summary.tsv'), ['name\\texit\\tseconds\\twhere', ...jobs.map(j => j.name + '\\t0\\t0.1\\tbox-1')].join('\\n') + '\\n')
`)
    writeFileSync(join(bin, 'supercomputer'), `#!/bin/sh\nexec '${process.execPath}' '${fake}' "$@"\n`, {mode: 0o755})
    for (const f of ['bar.ts', 'bar-lib.ts', 'bar-slots.ts']) cpSync(join(import.meta.dir, f), join(src, 'gates', f))
    put(join(src, 'package.json'), '{}\n')
    put(join(src, '.gitignore'), 'ignored.txt\n*.tmp\nnode_modules/\n')
    put(join(src, 'ignored.txt'), 'tracked despite ignore\n')
    put(join(src, 'payload.txt'), 'base\n')
    put(join(src, 'supercomputer/suite.json'), JSON.stringify([{name: 'run-proofs', cmd: 'true'}, {name: 'other', cmd: 'true'}]) + '\n')
    const library = join(dir, 'library'); mkdirSync(library)
    git(library, 'init', '-q')
    put(join(library, '.gitignore'), 'kept.dat\n*.tmp\n'); put(join(library, 'kept.dat'), 'vendored tracked ignored file\n')
    git(library, 'add', '-f', '.gitignore', 'kept.dat')
    const message = join(dir, 'message'); put(message, 'test: fixture\n')
    git(library, 'commit', '-q', '-F', message)
    git(src, 'init', '-q'); git(src, '-c', 'protocol.file.allow=always', 'submodule', 'add', '-q', library, 'vendor/lib')
    git(src, 'add', '.'); git(src, 'add', '-f', 'ignored.txt'); git(src, 'commit', '-q', '-F', message)
    const sha = git(src, 'rev-parse', 'HEAD'), common = git(src, 'rev-parse', '--path-format=absolute', '--git-common-dir')
    put(join(src, 'payload.txt'), 'dirty\n'); put(join(src, 'new file.txt'), 'untracked source\n'); put(join(src, 'ignored.tmp'), 'do not ship\n')
    const key = () => {
      const h = new Bun.CryptoHasher('sha256'); h.update(git(src, 'status', '--porcelain', '--untracked-files=all') + git(src, 'diff', 'HEAD'))
      for (const f of git(src, 'ls-files', '-o', '--exclude-standard').split('\n').filter(Boolean)) h.update(f + '\0' + readFileSync(join(src, f)).toString('base64'))
      return `${sha.slice(0, 12)}+${h.digest('hex').slice(0, 8)}`
    }
    const firstKey = key()
    for (const name of ['fresh', 'reuse', 'legacy']) {
      if (name === 'legacy') {
        put(join(src, 'payload.txt'), 'another dirty version\n')
        const old = join(store, 'trees', key()); mkdirSync(old, {recursive: true}); put(join(old, '.bar-ready'), key() + '\n'); put(join(old, 'stale.tmp'), 'old cache\n')
      }
      const expectedKey = key(), snapshot = join(store, 'trees', expectedKey)
      const p = start([process.execPath, join(src, 'gates/bar.ts'), '--base', sha, '--cand', src, '--only', 'suite', '--together', '--reruns', '0', '--name', name], src, env)
      children.push(p); const r = await result(p); expect(r.code, r.err).toBe(0)
      const report = JSON.parse(readFileSync(join(store, 'runs', name, 'report.json'), 'utf8'))
      expect(report.trees.cand.key).toBe(expectedKey)
      expect(report.results[0].error).toBeUndefined()
      const pilotDir = name === 'reuse' ? 'fresh' : name
      const receipt = JSON.parse(readFileSync(join(store, 'runs', pilotDir, 'suite/pilot-cand/root.json'), 'utf8'))
      expect(receipt.root).toBe(snapshot); expect(receipt.common).toBe(common)
      expect(JSON.parse(readFileSync(join(store, 'runs', pilotDir, 'suite/pilot-cand.jobs.json'), 'utf8')).map((j: {name: string}) => j.name)).toEqual(['run-proofs'])
      expect(report.suite.candidate).toMatchObject({passed: 2, failed: 0, jobs: 2})
      for (const f of ['ignored.txt', 'vendor/lib/kept.dat', 'new file.txt']) expect(receipt.files).toContain(f)
      expect(receipt.files).not.toContain('ignored.tmp')
      expect(readFileSync(join(snapshot, 'payload.txt'), 'utf8')).toBe(readFileSync(join(src, 'payload.txt'), 'utf8'))
      expect(readFileSync(join(snapshot, '.bar-ready'), 'utf8').trim()).toBe(expectedKey)
      put(join(snapshot, 'late-goals.json'), '{}\n')
      expect(git(snapshot, 'ls-files', '-o', '--exclude-standard')).toContain('late-goals.json')
      if (name !== 'legacy') expect(expectedKey).toBe(firstKey)
      else expect(existsSync(join(snapshot, 'stale.tmp'))).toBe(false)
    }
  } finally { await Promise.all(children.map(stop)); rmSync(dir, {recursive: true, force: true}) }
}, 60_000)

test('report CLI rejects zero candidate coverage per view and preserves the failed report', async () => {
  const dir = temp(), bin = join(dir, 'bin'), children: Child[] = []
  mkdirSync(bin)
  writeFileSync(join(bin, 'git'), `#!/bin/sh\nprintf '%s\\n' '${dir}/repo/.git'\n`, {mode: 0o755})
  const env = {...process.env, PATH: `${bin}:${process.env.PATH}`, GDPW_BAR_DIR: join(dir, 'bar')}
  const empty = join(dir, 'empty'), solved = join(dir, 'solved'), unsolved = join(dir, 'unsolved')
  const candIts = join(dir, 'cand-its'), baseIts = join(dir, 'base-its')
  for (const d of [empty, solved, unsolved, candIts, baseIts]) mkdirSync(d)
  for (const [d, outcome] of [[solved, 'proven'], [unsolved, 'unknown']])
    writeFileSync(join(d!, 'g332__fixture.log'), JSON.stringify({goal: 'fixture', outcome, searchMs: 1, leaves: 0, splits: 0}) + '\n')
  const row = (tool: string) => JSON.stringify({tool, task: 'fixture', answer: 'terminates', seconds: 1}) + '\n'
  writeFileSync(join(candIts, 'results.jsonl'), row('gdp'))
  writeFileSync(join(baseIts, 'results.jsonl'), row('gdp') + row('gdp-scc'))
  const cases = [
    {name: 'empty-candidate', group: 'g332', cand: empty, base: solved, error: 'g332'},
    {name: 'missing-directory', group: 'g332', cand: join(dir, 'absent'), base: solved, error: 'g332'},
    {name: 'later-baseline', group: 'g332', cand: empty, base: `${empty},${solved}`, error: 'g332'},
    {name: 'empty-both', group: 'g332', cand: empty, base: empty},
    {name: 'candidate-only', group: 'g332', cand: solved, base: ''},
    {name: 'unsolved-is-coverage', group: 'g332', cand: unsolved, base: solved},
    {name: 'second-view-empty', group: 'its', cand: candIts, base: baseIts, error: 'its-scc'},
  ]
  try {
    for (const c of cases) {
      const out = join(dir, c.name), message = `${c.error}: zero candidate goals against a nonempty baseline`
      const p = start([process.execPath, bar, 'compare', '--group', c.group, '--cand', c.cand, '--base', c.base,
        '--cand-tree', dir, '--base-tree', dir, '--out', out], dir, env)
      children.push(p)
      const r = await result(p)
      expect(r.code, r.err).toBe(c.error ? 1 : 0)
      const report = JSON.parse(readFileSync(join(out, 'report.json'), 'utf8'))
      expect(report.coverageErrors).toEqual(c.error ? [message] : [])
      if (c.error) {
        expect(r.err).toContain(message)
        expect(readFileSync(join(out, 'REPORT.md'), 'utf8')).toContain(`**ERROR: ${message}.**`)
        const replay = start([process.execPath, bar, 'report', out], dir, env); children.push(replay)
        const again = await result(replay)
        expect(again.code).toBe(1); expect(again.err).toContain(message)
      }
    }
  } finally { await Promise.all(children.map(stop)); rmSync(dir, {recursive: true, force: true}) }
}, 30_000)
