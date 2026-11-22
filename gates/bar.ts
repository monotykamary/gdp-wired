// The bar: a candidate against a base on every benchmark it can launch, in one command, and one report.
//
//   bun gates/bar.ts [--cand <rev | dir>] [--base <rev>] [--only f1,rw,...] [--quick] [--together]
//                    [--runs 3] [--reruns 3] [--procs 6] [--max-boxes N] [--name <out>]
//   bun gates/bar.ts baseline --base <rev> [--runs 3] [--only ...]     the shared baseline alone
//   bun gates/bar.ts devset [--from <base key>] [--write]             the quick mode's dev sets from a baseline
//   bun gates/bar.ts read <view> <run dir>...                         a run directory's headline, as the bar reads it
//   bun gates/bar.ts report <bar run dir>                             the report again from its report.json
//   bun gates/bar.ts compare --group g --cand d --base d1,d2 [...]    run directories made elsewhere, compared
//   bun gates/bar.ts failed <pass dir>...                             a pass's jobs that no box answered (lost or missing)
//
// Groups (`--only`): f1 and f2 (the frontier corpora), rw (the real-world corpus), suite and suite-usual
// (supercomputer/suite.json, by default and with GDP_CERT=usual, one mode after the other), onecpu (the 5 s-limited
// tests on one vCPU, ten jobs a side, each alone on a box of its own). The groups whose runners were Modal's (chc, its,
// sv, tip, g332, and lean, which samples the ITS run) were retired with those runners: `compare` and `report` still
// read their run directories, and `--only` refuses them.
//
// The candidate is a commit (a worktree is made for it under <main>/runs/bar/trees/) or a directory, run as it is
// (default: this checkout). The base (default: main) comes from the shared baseline, <main>/runs/bar/base/<sha>-instabox-r<v>/:
// N full runs of it (--runs, 3), made once and reused by every candidate; `--together` launches the base beside the
// candidate instead. Tasks whose first-pass verdict differs from the base's (its majority over its runs) are run
// --reruns times more on each side, together. onecpu times the two sides, so its base always runs beside the candidate.
// `--quick` runs each benchmark's dev set (gates/bar-dev.json: stratified by family and by how main did) and predicts
// the full delta from it. Every pass is one `supercomputer run --jobs <pass>.jobs.json --out <pass>` in its side's tree
// (github.com/monotykamary/supercomputer, on instabox), read from <pass>/summary.tsv and the jobs' logs.
//
// Hygiene: each launch is a local `supercomputer run` client under a wall cap, stopped (SIGINT, then SIGTERM, then
// SIGKILL, by its exact pid) at it; on any exit the bar stops every client it started. A stopped client's jobs finish
// on their boxes within their own timeouts and the boxes pause themselves (`supercomputer batch fetch <pass>` picks a
// pass up again; every run reaps the paused boxes past their keep). Each tree's first launch of a group is a pilot of
// one or two tasks, read before the fan-out. instabox bills its boxes by the second and the bar has no bill to read:
// the report gives the job seconds.
import {closeSync, cpSync, existsSync, mkdirSync, lstatSync, openSync, readFileSync, readdirSync, realpathSync, rmSync, statSync, writeFileSync} from 'node:fs'
import {dirname, join, resolve} from 'node:path'
import {acquireBarSlot, type BarSlot} from './bar-slots.ts'
import {type Dev, type Obs, type Rows, type TaskCmp, VIEWS, compareTasks, differing, goalSig, goals, inBand, keyOfCmd, predict, summaryLines, testTimes, devSet} from './bar-lib.ts'

const VERSION = 1
const argv = process.argv.slice(2)
const sub = argv[0] && !argv[0].startsWith('--') ? argv.shift()! : 'run'
const opt = (k: string, d = '') => { const i = argv.indexOf(`--${k}`); return i < 0 ? d : argv[i + 1] ?? d }
const flag = (k: string) => argv.includes(`--${k}`)
// --smoke: the bar itself end to end on each group's pilot tasks, the base launched together (nothing cached)
const smoke = flag('smoke'), quick = flag('quick'), together = flag('together') || smoke
const nRuns = Number(opt('runs', '3')), nReruns = Number(opt('reruns', '3')), maxProcs = Number(opt('procs', '6')), maxBoxes = opt('max-boxes')
// (the jobs' tool: `supercomputer` on the PATH, or the one SUPERCOMPUTER_BIN names)
const SC = process.env.SUPERCOMPUTER_BIN ?? 'supercomputer'
const SUBS = ['run', 'baseline', 'devset', 'read', 'report', 'failed', 'compare']
// What the bar no longer takes: the backend (instabox only), the Modal-billed budget, TIP's rivals (Modal's runner)
const GONE: Record<string, string> = {
  backend: 'every pass runs on instabox through `supercomputer run`',
  budget: "instabox's spend isn't reported to the bar (the report gives the job seconds)",
  rivals: "TIP's runner was Modal's and was retired",
}

// ------------------------------------------------------------------------------------------------------- the shell
const out0 = (args: string[], cwd?: string, trim = true) => {
  const p = Bun.spawnSync(args, {cwd, stdout: 'pipe', stderr: 'pipe'})
  if (p.exitCode !== 0) throw new Error(`${args.join(' ')}: ${p.stderr.toString().slice(-600)}`)
  return trim ? p.stdout.toString().trim() : p.stdout.toString()
}
const HERE = dirname(import.meta.path)
const MAIN = dirname(out0(['git', 'rev-parse', '--path-format=absolute', '--git-common-dir'], HERE))
const BAR = process.env.GDPW_BAR_DIR ?? join(MAIN, 'runs', 'bar')
const log = (...a: unknown[]) => console.log(`[bar ${new Date().toISOString().slice(11, 19)}]`, ...a)
const mkdir = (d: string) => mkdirSync(d, {recursive: true})
const readJson = <T>(f: string): T => JSON.parse(readFileSync(f, 'utf8')) as T
const writeJson = (f: string, x: unknown) => { mkdir(dirname(f)); writeFileSync(f, JSON.stringify(x, null, 1) + '\n') }

let stopping = false
let barSlot: BarSlot | undefined
type Child = {pid: number, kill: (s: NodeJS.Signals) => void, what: string, cwd: string}
const live = new Map<number, Child>()
let slots = maxProcs
const waiting: (() => void)[] = []
const acquire = async () => { while (slots <= 0) await new Promise<void>(r => waiting.push(r)); slots-- }
const release = () => { slots++; waiting.shift()?.() }

// One launch: argv (no shell, so the pid is the client's own), its output to a log, stopped at its wall cap.
async function run(args: string[], o: {cwd: string, log: string, stdout?: string, env?: Record<string, string>, cap: number}): Promise<number> {
  await acquire()
  if (stopping) { release(); return 130 }  // nothing new once the bar is stopping
  mkdir(dirname(o.log))
  const fd = openSync(o.log, 'a'), sfd = o.stdout ? openSync(o.stdout, 'w') : fd
  try {
    const p = Bun.spawn(args, {cwd: o.cwd, stdout: sfd, stderr: fd, env: {...process.env, ...o.env}})
    const c: Child = {pid: p.pid, kill: s => p.kill(s), what: args.slice(0, 3).join(' '), cwd: o.cwd}
    live.set(p.pid, c)
    const timer = setTimeout(() => { log(`cap of ${o.cap} s reached: stopping ${c.what} (pid ${c.pid})`); void stop(c) }, o.cap * 1000)
    const code = await p.exited
    clearTimeout(timer)
    live.delete(p.pid)
    return code
  } finally {
    closeSync(fd)
    if (o.stdout) closeSync(sfd)
    release()
  }
}
// SIGINT first (a client's Ctrl-C), SIGTERM, SIGKILL last; a stopped client's jobs finish where they run.
async function stop(c: Child) {
  for (const [s, wait] of [['SIGINT', 45], ['SIGTERM', 45], ['SIGKILL', 5]] as const) {
    if (!live.has(c.pid)) return
    try { c.kill(s) } catch { return }
    for (let i = 0; i < wait && live.has(c.pid); i++) await Bun.sleep(1000)
  }
}
async function stopAll(why: string) {
  if (stopping) return
  stopping = true
  log(`stopping ${live.size} launch(es): ${why}`)
  await Promise.all([...live.values()].map(stop))
}
for (const s of ['SIGINT', 'SIGTERM', 'SIGHUP'] as const) process.on(s, () => { void stopAll(s).then(() => process.exit(130)) })
function finishAdmission() { barSlot?.release(); barSlot = undefined }
process.on('exit', () => {
  for (const c of live.values()) try { c.kill('SIGINT') } catch { /* gone */ }
  finishAdmission()
})

// ------------------------------------------------------------------------------------------------------- the trees
type Tree = {path: string, sha: string, key: string, clean: boolean, label: string}
// A directory with no uncommitted changes is its commit's tree; one with changes is copied (what git sees, untracked
// files too, without node_modules, runs/ and .git) to <bar>/trees/<sha>+<hash of the changes>, so editing it while
// a pass packs it changes nothing, and the same changes are the same tree.
// A detached worktree keeps the tree `supercomputer run` packs (its git root's tracked and unignored files) correct.
function snapshotRoot(path: string, src: string): boolean {
  if (!existsSync(join(path, '.git'))) return false
  try {
    return out0(['git', 'rev-parse', '--show-toplevel'], path) === realpathSync(path) &&
      out0(['git', 'rev-parse', '--path-format=absolute', '--git-common-dir'], path) === out0(['git', 'rev-parse', '--path-format=absolute', '--git-common-dir'], src)
  } catch { return false }
}
// Flatten the source's Git-visible files into the snapshot's private index. rsync excludes submodule .git files,
// so leaving gitlinks in that index would silently omit their contents from the packer's git ls-files walk.
// Force-add preserves tracked-but-ignored files; later generated untracked assets must remain visible too.
function snapshotFiles(src: string, dst: string, prefix = ''): string[] {
  const files: string[] = []
  for (const f of out0(['git', 'ls-files', '-z', '-co', '--exclude-standard'], src, false).split('\0').filter(Boolean)) {
    const from = join(src, f), to = join(dst, f)
    let fromDir: boolean, toDir: boolean
    try { fromDir = lstatSync(from).isDirectory(); toDir = lstatSync(to).isDirectory() }
    catch { continue } // deleted or excluded by the snapshot copy
    if (fromDir) {
      if (existsSync(join(from, '.git'))) files.push(...snapshotFiles(from, to, prefix + f + '/'))
    } else if (!toDir) files.push(prefix + f)
  }
  return files
}
function treeOf(rev: string): Tree {
  if (existsSync(rev) && statSync(rev).isDirectory()) {
    const src = realpathSync(rev), sha = out0(['git', 'rev-parse', 'HEAD'], src)
    const dirt = out0(['git', 'status', '--porcelain', '--untracked-files=all'], src)
    if (!dirt) return {...treeOf(sha), label: `${src} at ${sha.slice(0, 12)}`}
    const h = new Bun.CryptoHasher('sha256')
    h.update(dirt + out0(['git', 'diff', 'HEAD'], src))
    for (const f of out0(['git', 'ls-files', '-o', '--exclude-standard'], src).split('\n').filter(Boolean)) h.update(f + '\0' + (existsSync(join(src, f)) ? readFileSync(join(src, f)).toString('base64') : ''))
    const key = `${sha.slice(0, 12)}+${h.digest('hex').slice(0, 8)}`, path = join(BAR, 'trees', key)
    if (!existsSync(join(path, '.bar-ready')) || !snapshotRoot(path, src)) {
      log(`copying ${src} (uncommitted changes) to ${path}`)
      if (!snapshotRoot(path, src)) {
        // Repair old rsync-only caches as well as creating new ones; --force permits an interrupted registration.
        rmSync(path, {recursive: true, force: true})
        mkdir(dirname(path))
        out0(['git', 'worktree', 'add', '--force', '--detach', '--no-checkout', path, sha], src)
      }
      out0(['rsync', '-a', '--delete', '--exclude', 'node_modules/', '--exclude', '/runs/', '--exclude', '.git', '--exclude', '*.olean', '--exclude', '*.ilean', '--exclude', '.lake/', '--exclude', '.bar-lean/', `${src}/`, `${path}/`])
      const manifest = join(out0(['git', 'rev-parse', '--absolute-git-dir'], path), 'bar-files')
      writeFileSync(manifest, snapshotFiles(src, path).join('\0') + '\0')
      out0(['git', 'read-tree', '--empty'], path)
      out0(['git', '--literal-pathspecs', 'add', '-f', `--pathspec-from-file=${manifest}`, '--pathspec-file-nul'], path)
      out0(['bun', 'install', '--frozen-lockfile'], path)
      writeFileSync(join(path, '.bar-ready'), key + '\n')
    }
    return {path, sha, clean: false, key, label: `${src} (uncommitted changes, copied as ${key})`}
  }
  const sha = out0(['git', 'rev-parse', '--verify', `${rev}^{commit}`], MAIN)
  const path = join(BAR, 'trees', sha.slice(0, 12))
  mkdir(join(BAR, 'trees'))
  if (!existsSync(join(path, '.bar-ready'))) {
    log(`making the tree of ${sha.slice(0, 12)} at ${path}`)
    if (!existsSync(path)) out0(['git', 'worktree', 'add', '--detach', path, sha], MAIN)
    out0(['git', '-c', 'protocol.file.allow=always', 'submodule', 'update', '--init'], path) // the main checkout's submodules may be local paths (a worktree's clone): allowed here only
    out0(['bun', 'install', '--frozen-lockfile'], path)
    writeFileSync(join(path, '.bar-ready'), sha + '\n')
  }
  return {path, sha, clean: true, key: sha.slice(0, 12), label: `${rev} (${sha.slice(0, 12)})`}
}
// A tree from before the move to instabox has the old tool's supercomputer.toml ([boat], [modal]), which `supercomputer
// run` refuses: it gets this checkout's (what its boxes need), so both sides run on one image. The trees are the bar's.
const OWN_CONFIG = join(HERE, '..', 'supercomputer.toml')
function configure(tree: string) {
  const f = join(tree, 'supercomputer.toml')
  if (!existsSync(OWN_CONFIG) || resolve(f) === resolve(OWN_CONFIG)) return
  const t = existsSync(f) ? readFileSync(f, 'utf8') : ''
  if (!/^\[instabox\]/m.test(t) || /^\[(boat|modal|treadmill|gpu|runpod)\]/m.test(t)) cpSync(OWN_CONFIG, f)
}

// -------------------------------------------------------------------------------------------------------- the groups
type Side = 'cand' | 'base'
type Pass = {group: string, side: Side, tree: Tree, dir: string, tasks?: string[], quickSize?: boolean}
// A job of a `supercomputer run` jobs file (suite.json's extra fields pass through: the tool reads only its own)
type Job = {name: string, cmd: string, cwd?: string, cpu?: number, memory?: number, timeout?: number, env?: Record<string, string>, image?: string, vm_type?: string}
// (launch: none for a group retired with its Modal runner: compare and report still read its run directories)
type Group = {key: string, views: string[], cap: number, launch?: (p: Pass) => Promise<number>, pairAlways?: boolean, noRerun?: boolean, candOnly?: boolean, after?: string, inQuick: boolean}

// One pass: its jobs (those it was given) as <pass>.jobs.json, their keys as <pass>.keys.json, one `supercomputer run`.
// The tool exits 3 when a job failed (a failing test is data) or was lost (no box answered it within its attempts:
// the pass's meta lists them); once it has written summary.tsv that is a pass that ran, 0 here.
async function jobsPass(p: Pass, jobs: Job[], keyOf: (j: Job) => string, cap: number, o: {timing?: boolean} = {}) {
  const keep = p.tasks ? new Set(p.tasks) : undefined, js = keep ? jobs.filter(j => keep.has(keyOf(j))) : jobs
  writeJson(`${p.dir}.jobs.json`, js)
  writeJson(`${p.dir}.keys.json`, Object.fromEntries(js.map(j => [j.name, keyOf(j)])))
  if (!js.length) { mkdir(p.dir); return 0 }
  configure(p.tree.path)
  const code = await run([SC, 'run', '--jobs', `${p.dir}.jobs.json`, '--out', p.dir, ...(maxBoxes ? ['--max-boxes', maxBoxes] : []), ...(o.timing ? ['--timing'] : [])],
    {cwd: p.tree.path, log: `${p.dir}.log`, cap})
  return code === 3 && existsSync(join(p.dir, 'summary.tsv')) ? 0 : code
}
async function jobsOf(p: Pass, args: string[]): Promise<Job[]> {
  const f = `${p.dir}.all-jobs.json`
  mkdir(dirname(f))
  const code = await run(args, {cwd: p.tree.path, log: `${p.dir}.log`, stdout: f, cap: 300})
  if (code !== 0) throw new Error(`${args.join(' ')} exit ${code}`)
  return readJson<Job[]>(f)
}
const corpusPass = (corpus: string) => async (p: Pass) => {
  const jobs = await jobsOf(p, ['bun', `research/${corpus}/jobs.ts`])
  mkdir(p.dir)
  // the broken variants, which count when refused (research/<corpus>/score.ts's tally)
  await run(['bun', '-e', `const {corpus} = await import('./research/${corpus}/corpus.ts'); console.log(JSON.stringify(corpus.filter(i => i.broken).map(i => i.id)))`],
    {cwd: p.tree.path, log: `${p.dir}.log`, stdout: `${p.dir}/broken.json`, cap: 300})
  return jobsPass(p, jobs, j => keyOfCmd(j.cmd) ?? j.name, 1800)
}
const suiteJobs = (p: Pass) => readJson<Job[]>(join(p.tree.path, 'supercomputer', 'suite.json'))
const GROUPS: Group[] = [
  {key: 'f1', views: ['f1'], cap: 1800, inQuick: true, launch: corpusPass('frontier')},
  {key: 'f2', views: ['f2'], cap: 1800, inQuick: true, launch: corpusPass('frontier2')},
  {key: 'rw', views: ['rw'], cap: 1800, inQuick: true, launch: async p => jobsPass(p, await jobsOf(p, ['bun', 'research/realworld/jobs.ts']), j => keyOfCmd(j.cmd) ?? j.name, 1800)},
  {key: 'suite', views: ['suite'], cap: 2400, inQuick: false, launch: p => jobsPass(p, suiteJobs(p), j => j.name, 2400)},
  // (--usual: each proof's certificate the usual trees, and the Lean export reading those: core/cyclic.ts's certOn)
  {key: 'suite-usual', views: ['suite-usual'], cap: 2400, inQuick: false, after: 'suite',
    launch: p => jobsPass(p, suiteJobs(p).map(j => ({...j, env: {...j.env, GDP_CERT: 'usual'}})), j => j.name, 2400)},
  // (each job alone on a box of its own, `--timing`, and on one of its vCPUs by taskset)
  {key: 'onecpu', views: [], cap: 1500, inQuick: true, pairAlways: true, noRerun: true, launch: p => {
    const n = smoke ? 1 : p.quickSize ? 3 : 10, jobs: Job[] = []
    for (let i = 0; i < n; i++) for (const t of ['data', 'infer']) jobs.push({name: `${p.side}-${t}-${i}`, cmd: `bun install --frozen-lockfile >/dev/null 2>&1; taskset -c 0 bun test core/${t}.test.ts 2>&1`, cpu: 1.0, timeout: 600})
    return jobsPass(p, jobs, j => j.name, 1500, {timing: true})
  }},
]
// Retired with their Modal runners (compare/chc/modal_chc.py, compare/term/modal_term.py and modal_sv.py,
// compare/tip/modal_tip.py, research/query/modal_query.py; lean sampled the ITS run): read, never launched.
const RETIRED: Group[] = [
  {key: 'chc', views: ['chc'], cap: 0, inQuick: false},
  {key: 'its', views: ['its', 'its-scc'], cap: 0, inQuick: false},
  {key: 'sv', views: ['sv', 'sv-scc'], cap: 0, inQuick: false},
  {key: 'tip', views: ['tip', 'tip-cvc5', 'tip-cvc5cg', 'tip-vampire'], cap: 0, inQuick: false},
  {key: 'g332', views: ['g332'], cap: 0, inQuick: false, pairAlways: true, noRerun: true},
  {key: 'lean', views: ['lean'], cap: 0, inQuick: false, candOnly: true, noRerun: true},
]
const groupOf = (k: string) => [...GROUPS, ...RETIRED].find(g => g.key === k)

// ------------------------------------------------------------------------------------------------------ the dev set
const DEV_FILE = join(HERE, 'bar-dev.json')
// A group's pilot when the dev file names none: two fast solved tasks of main's runs.
const PILOT: Record<string, string[]> = {
  f1: ['nonlinear/cauchy-schwarz', 'nonlinear/cubes'], f2: ['term/Continue1.jar-obl-8', 'chc/H/durationThm_1_e1_197'],
  rw: ['feature flag/growthbook/forceRuleRollout#6', 'feature flag/growthbook/forceRuleRollout#4'],
  suite: ['run-proofs'], 'suite-usual': ['run-proofs'],
}
type DevFile = {made: string, views: Record<string, Dev>, pilot: Record<string, string[]>}
const devFile = (): DevFile | undefined => existsSync(DEV_FILE) ? readJson<DevFile>(DEV_FILE) : undefined
const groupDev = (g: Group): string[] | undefined => {
  const d = devFile()
  if (!d) throw new Error(`--quick needs ${DEV_FILE} (bun gates/bar.ts devset --write)`)
  const ts = g.views.flatMap(v => Object.keys(d.views[v]?.tasks ?? {}))
  return ts.length ? [...new Set(ts)].sort() : undefined
}

// -------------------------------------------------------------------------------------------------- the passes run
const views = (g: Group) => g.views.map(v => VIEWS[v]!)
const parse = (g: Group, dir: string, tree: Tree) => new Map(views(g).map(v => [v.key, v.parse(dir, tree.path)]))
// (batch: the pass's `supercomputer` batch id, boxes: how many boxes its jobs ran on, lost: the jobs no box answered)
type Meta = {group: string, side: Side, tree: string, sha: string, started: string, wall_s: number, code: number, tasks: number | 'all', batch?: string, boxes?: number, lost?: string[]}

async function pass(g: Group, p: Pass): Promise<Meta> {
  const t0 = Date.now(), started = new Date().toISOString()
  mkdir(dirname(p.dir))
  if (p.tasks) writeJson(`${p.dir}.given.json`, p.tasks)
  let code: number
  try { code = await g.launch!(p) } catch (e) { writeFileSync(`${p.dir}.log`, `\n${String(e)}\n`, {flag: 'a'}); code = -1 }
  const lost = lostJobs(p.dir)
  const batch = existsSync(join(p.dir, 'batch.json')) ? readJson<{id?: string}>(join(p.dir, 'batch.json')).id : undefined
  const boxes = new Set(summaryLines(p.dir).map(r => r.where).filter(Boolean)).size
  const m: Meta = {group: g.key, side: p.side, tree: p.tree.label, sha: p.tree.sha, started, wall_s: Math.round((Date.now() - t0) / 100) / 10, code, tasks: p.tasks?.length ?? 'all',
    batch, boxes, lost: lost.length ? lost : undefined}
  writeJson(`${p.dir}.meta.json`, m)
  log(`${g.key} ${p.side} ${p.dir.split('/').at(-1)}: exit ${code}, ${m.wall_s} s${batch ? `, batch ${batch} on ${boxes} box(es)` : ''}${lost.length ? `, ${lost.length} job(s) lost (supercomputer batch fetch ${p.dir})` : ''}`)
  return m
}

// A pass's jobs no box answered: a summary row `lost` (its attempts spent on boxes that went away) or no row at all
// (the client stopped before the batch ended: `supercomputer batch fetch <pass>` picks it up).
function lostJobs(dir: string): string[] {
  if (!existsSync(`${dir}.keys.json`)) return []
  const keys = readJson<Record<string, string>>(`${dir}.keys.json`), rows = new Map(summaryLines(dir).map(r => [r.name, r]))
  return Object.entries(keys).filter(([job]) => !rows.has(job) || rows.get(job)!.code === 'lost').map(([, key]) => key)
}

// The pilot: one or two tasks of the group in this tree, end to end, read before its fan-out (once per tree).
async function pilot(g: Group, tree: Tree, side: Side, outDir: string): Promise<string | undefined> {
  if (g.noRerun || g.candOnly || smoke) return undefined
  const ok = join(BAR, 'pilots', `${tree.key}-instabox-${g.key}-r${VERSION}.ok`)
  if (existsSync(ok)) return undefined
  const tasks = devFile()?.pilot[g.key] ?? PILOT[g.key]
  const p: Pass = {group: g.key, side, tree, dir: join(outDir, g.key, `pilot-${side}`), tasks}
  const m = await pass(g, p)
  const rows = [...parse(g, p.dir, tree).values()][0] ?? new Map()
  const good = [...rows.values()].filter(o => o.answer !== 'error' && o.answer !== 'missing' && o.answer !== 'exit lost' && !o.answer.startsWith('exit -'))
  if (m.code !== 0 && !rows.size) return `the pilot exited ${m.code} with no rows (${p.dir}.log)`
  if (!good.length) return `the pilot's ${rows.size} rows are all errors (${p.dir})`
  writeJson(ok, {at: new Date().toISOString(), dir: p.dir, rows: [...rows].map(([t, o]) => `${t}: ${o.answer} ${o.secs}`)})
  return undefined
}

// The shared baseline: N full runs of the base per group, under a lock, each kept once it ends (`.done`) with every
// job answered.
const cacheDir = (tree: Tree) => join(BAR, 'base', `${tree.key}-instabox-r${VERSION}`)
async function baseline(g: Group, tree: Tree, n: number, outDir: string): Promise<string[]> {
  if (!tree.clean) throw new Error(`the base ${tree.label} has uncommitted changes: use --together`)
  const gdir = join(cacheDir(tree), g.key), lock = join(gdir, '.lock')
  const done = () => Array.from({length: n}, (_, i) => join(gdir, `run${i + 1}`)).filter(d => existsSync(`${d}/.done`))
  mkdir(gdir)
  let waited = false
  for (;;) {
    if (done().length >= n) return done()
    try {
      mkdirSync(lock)
      writeFileSync(join(lock, 'pid'), String(process.pid))
      break
    } catch {
      const pid = Number(existsSync(join(lock, 'pid')) ? readFileSync(join(lock, 'pid'), 'utf8') : 0)
      let alive = false
      try { process.kill(pid, 0); alive = pid > 0 } catch { alive = false }
      if (!alive) { rmSync(lock, {recursive: true, force: true}); continue }
      if (!waited) log(`${g.key}: the baseline is being made by pid ${pid}; waiting`)
      waited = true
      await Bun.sleep(20_000)
    }
  }
  try {
    const why = await pilot(g, tree, 'base', outDir)
    if (why) throw new Error(`${g.key} base pilot: ${why}`)
    const missing = Array.from({length: n}, (_, i) => join(gdir, `run${i + 1}`)).filter(d => !existsSync(`${d}/.done`))
    // one run after the other, so the runs see the machines at different times and their band holds that noise too
    log(`${g.key}: making ${missing.length} baseline run(s) of ${tree.label}, one after the other`)
    for (const d of missing) {
      if (stopping) break
      rmSync(d, {recursive: true, force: true})
      const m = await pass(g, {group: g.key, side: 'base', tree, dir: d})
      if (m.code === 0 && !m.lost && [...parse(g, d, tree).values()].some(r => r.size)) writeJson(`${d}/.done`, m)
      else log(`${g.key}: the baseline run ${d} exited ${m.code}${m.lost ? ` with ${m.lost.length} job(s) lost` : ''}: not kept`)
    }
    return done()
  } finally { rmSync(lock, {recursive: true, force: true}) }
}

type Result = {group: string, cand?: string, base: string[], reruns: {cand: string[], base: string[]}, differing: string[], quick?: string[], error?: string, metas: Meta[]}
// Each group's first pass, a side at a time, as gates the groups that follow one wait on (suite-usual after suite,
// side by side).
type Gate = {p: Promise<unknown>, open: (x?: unknown) => void}
const gates = new Map<string, Gate>()
const gate = (k: string): Gate => {
  if (!gates.has(k)) { let open: (x?: unknown) => void = () => {}; const p = new Promise<unknown>(r => { open = r }); gates.set(k, {p, open}) }
  return gates.get(k)!
}
async function groupFlow(g: Group, cand: Tree, base: Tree, outDir: string, inRun: Set<string>): Promise<Result> {
  const res: Result = {group: g.key, base: [], reruns: {cand: [], base: []}, differing: [], metas: []}
  const tasks = g.key === 'onecpu' ? undefined : smoke ? devFile()?.pilot[g.key] ?? PILOT[g.key] : quick ? groupDev(g) : undefined
  res.quick = tasks
  const gd = join(outDir, g.key)
  const after = g.after && inRun.has(g.after) ? g.after : undefined
  const sidePass = async (side: Side, tree: Tree): Promise<string> => {
    if (after) await gate(`${after}/${side}`).p
    const why = await pilot(g, tree, side, outDir)
    if (why) throw new Error(`${side} pilot: ${why}`)
    const p: Pass = {group: g.key, side, tree, dir: join(gd, `${side}-1`), tasks, quickSize: quick}
    res.metas.push(await pass(g, p))
    return p.dir
  }
  try {
    const basePromise: Promise<string[]> = g.candOnly ? Promise.resolve([]) : together || g.pairAlways ? sidePass('base', base).then(d => [d])
      : (after ? gate(`${after}/base`).p : Promise.resolve()).then(() => baseline(g, base, nRuns, outDir))
    void basePromise.then(() => gate(`${g.key}/base`).open(), () => gate(`${g.key}/base`).open())
    const candPromise = sidePass('cand', cand)
    void candPromise.then(() => gate(`${g.key}/cand`).open(), () => gate(`${g.key}/cand`).open())
    const [c, b] = await Promise.allSettled([candPromise, basePromise])
    if (c.status === 'rejected') throw c.reason
    if (b.status === 'rejected') throw b.reason
    res.cand = c.value
    res.base = b.value
  } catch (e) {
    res.error = String(e)
    return res
  }
  if (g.noRerun || !res.base.length) return res
  const keep = tasks ? new Set(tasks) : undefined
  const restrict = (r: Rows) => keep ? new Map([...r].filter(([t]) => keep.has(t))) : r
  const D = new Set<string>()
  for (const v of views(g)) {
    const c = v.parse(res.cand, cand.path), bs = res.base.map(b => restrict(v.parse(b, base.path)))
    for (const t of differing(c, bs)) D.add(t)
  }
  res.differing = [...D].sort()
  if (!D.size || nReruns <= 0) return res
  if (D.size > 400) { res.error = `${D.size} tasks differ: not rerun (a broken candidate?)`; return res }
  if (stopping) { res.error = 'the bar is stopping: no reruns'; return res }
  log(`${g.key}: ${D.size} task(s) differ; ${nReruns} rerun(s) a side`)
  const reruns = (side: Side, tree: Tree) => Array.from({length: nReruns}, async (_, i) => {
    const p: Pass = {group: g.key, side, tree, dir: join(gd, `${side}-r${i + 1}`), tasks: res.differing}
    res.metas.push(await pass(g, p))
    res.reruns[side].push(p.dir)
  })
  await Promise.all([...reruns('cand', cand), ...reruns('base', base)])
  return res
}

// ------------------------------------------------------------------------------------------------------ job seconds
// The seconds every job of a directory's passes took (each pass's summary.tsv), lost jobs apart.
function jobSeconds(dir: string): number {
  let s = 0
  const walk = (d: string) => {
    for (const f of readdirSync(d, {withFileTypes: true})) {
      if (!f.isDirectory()) continue
      const p = join(d, f.name)
      if (existsSync(join(p, 'summary.tsv'))) for (const r of summaryLines(p)) s += r.code === 'lost' ? 0 : Math.max(0, Number(r.secs) || 0)
      else walk(p)
    }
  }
  if (existsSync(dir)) walk(dir)
  return Math.round(s * 10) / 10
}

// ------------------------------------------------------------------------------------------------------- the size
function size(tree: string) {
  let bytes = 0, lines = 0
  const walk = (d: string) => { for (const f of readdirSync(d, {withFileTypes: true})) { const p = join(d, f.name); if (f.isDirectory()) { if (f.name !== 'generated' && f.name !== 'node_modules') walk(p) } else if (f.name.endsWith('.ts') && !f.name.endsWith('.test.ts')) { const t = readFileSync(p); bytes += t.length; lines += t.toString().split('\n').length - 1 } } }
  for (const d of ['core', 'kernel']) if (existsSync(join(tree, d))) walk(join(tree, d))
  return {bytes, lines}
}

// ----------------------------------------------------------------------------------------------------- the report
const fmt = (n: number) => Number.isInteger(n) ? n.toLocaleString('en-US') : n.toLocaleString('en-US', {maximumFractionDigits: 2})
const sign = (n: number) => (n > 0 ? '+' : '') + fmt(n)
function consensus(rs: Rows[]): Rows {
  const out: Rows = new Map()
  for (const t of new Set(rs.flatMap(r => [...r.keys()]))) {
    const os = rs.map(r => r.get(t)).filter((o): o is Obs => !!o), k = os.filter(o => o.solved).length
    out.set(t, {...(os.find(o => o.solved === k * 2 > os.length) ?? os[0]!), solved: k * 2 > os.length})
  }
  return out
}
function report(results: Result[], cand: Tree, base: Tree, outDir: string, t0: number, since: Date): string {
  const L: string[] = [], J: Record<string, unknown> = {}, coverageErrors: string[] = []
  const p = (s = '') => L.push(s)
  p(`# The bar: ${cand.label} against ${base.label}`)
  p()
  p(`${quick ? 'Quick mode (each benchmark\'s dev set, gates/bar-dev.json)' : 'Full mode'}; on instabox (\`supercomputer run\`); the base ${together ? 'launched together' : `from the shared baseline (${nRuns} runs, ${cacheDir(base)})`}, except onecpu (always together); ${nReruns} rerun(s) a side of every task that differs. Started ${since.toISOString()}.`)
  p()
  const dev = devFile()
  for (const r of results) {
    const g = groupOf(r.group)!
    if (r.error) p(`**${g.key}: ${r.error}**\n`)
    for (const m of r.metas.filter(x => x.lost?.length)) p(`- ${g.key}, a ${m.side} launch: ${m.lost!.length} job(s) no box answered (${m.lost!.slice(0, 5).join(', ')}${m.lost!.length > 5 ? ', ...' : ''}); \`supercomputer batch fetch\` on its directory picks it up.\n`)
    for (const m of r.metas.filter(x => x.code !== 0)) p(`**${g.key}: a ${m.side} launch exited ${m.code} after ${m.wall_s} s (${m.tasks === 'all' ? 'every task' : `${m.tasks} tasks`}); its log is beside its directory.**\n`)
    if (!r.cand) continue
    if (g.key === 'onecpu') { onecpu(r, p); continue }
    for (const v of views(g)) {
      const keep = r.quick ? new Set(r.quick) : undefined
      const restrict = (x: Rows) => keep ? new Map([...x].filter(([t]) => keep.has(t))) : x
      const c = v.parse(r.cand, cand.path), bs = r.base.map(b => restrict(v.parse(b, base.path)))
      if (!c.size && !bs.some(b => b.size)) continue
      if (!c.size) {
        const error = `${v.key}: zero candidate goals against a nonempty baseline`
        coverageErrors.push(error)
        p(`**ERROR: ${error}.**\n`)
      }
      const hc = v.headline(c), hb = bs.map(b => v.headline(b)), keys = Object.keys(hc)
      const mean = Object.fromEntries(keys.map(k => [k, hb.length ? Math.round(hb.reduce((s, h) => s + (h[k] ?? 0), 0) / hb.length * 100) / 100 : NaN]))
      p(`## ${v.title}${r.quick ? ` (${smoke ? 'smoke' : 'dev set'}: ${fmt(r.quick.length)} tasks)` : ''}`)
      p()
      p(`| side | ${keys.join(' | ')} |`)
      p(`| --- | ${keys.map(() => '---').join(' | ')} |`)
      p(`| candidate | ${keys.map(k => fmt(hc[k]!)).join(' | ')} |`)
      hb.forEach((h, i) => p(`| base run ${i + 1} | ${keys.map(k => fmt(h[k] ?? 0)).join(' | ')} |`))
      if (hb.length > 1) p(`| base mean | ${keys.map(k => fmt(mean[k]!)).join(' | ')} |`)
      if (hb.length) p(`| delta (candidate - base mean) | ${keys.map(k => sign(Math.round((hc[k]! - mean[k]!) * 100) / 100)).join(' | ')} |`)
      p()
      const sample = new Map<string, {cand: Obs[], base: Obs[]}>()
      const D = r.differing.filter(t => c.has(t))
      const rc = r.reruns.cand.map(d => v.parse(d, cand.path)), rb = r.reruns.base.map(d => v.parse(d, base.path))
      for (const t of D) sample.set(t, {cand: [c, ...rc].map(x => x.get(t)).filter((o): o is Obs => !!o), base: [...bs, ...rb].map(x => x.get(t)).filter((o): o is Obs => !!o)})
      const cmp = compareTasks(D, sample, v.limit)
      const n = (k: TaskCmp['kind'], f: (x: TaskCmp) => boolean = () => true) => cmp.filter(x => x.kind === k && f(x)).length
      if (g.key !== 'lean' && bs.length) {
        const outside = D.filter(t => !inBand(bs.map(b => b.get(t)).filter((o): o is Obs => !!o), v.limit))
        const only = (side: 'cand' | 'base') => D.filter(t => side === 'cand' ? !!c.get(t)?.solved : !c.get(t)?.solved).length
        p(`- ${fmt(D.length)} differ in the first pass (${only('cand')} solved by the candidate only, ${only('base')} by the base only; ${fmt(outside.length)} outside the base's noise band: its runs agreeing and no answer in the last quarter of the ${v.limit} s limit); after ${r.reruns.cand.length} rerun(s) a side:` +
          ` **gained ${n('gained')}** (${n('gained', x => x.solid)} in every run against none), **lost ${n('lost')}** (${n('lost', x => x.solid)} solid), noise ${n('noise')}, wrong ${n('wrong')}; answered only past ${0.75 * v.limit} s in some run (a flip at the time limit): ${cmp.filter(x => x.atLimit && x.kind === 'gained').length} of the gained, ${cmp.filter(x => x.atLimit && x.kind === 'lost').length} of the lost.`)
        if (r.quick && dev?.views[v.key]) {
          const pr = predict(dev.views[v.key]!, c, consensus(bs))
          p(`- Predicted full-set delta from the dev set: ${sign(pr.scaled)} (raw ${sign(pr.raw)} on ${fmt(Object.keys(dev.views[v.key]!.tasks).length)} tasks; calibration in gates/README.md).`)
        }
        const show = cmp.filter(x => x.kind !== 'noise').sort((a, b) => a.kind.localeCompare(b.kind) || a.task.localeCompare(b.task))
        if (show.length) {
          p()
          p('| task | verdict | candidate solved | base solved | at the limit | answers (candidate / base, seconds) |')
          p('| --- | --- | --- | --- | --- | --- |')
          const os = (xs: Obs[]) => xs.map(o => `${o.answer} ${fmt(Math.round(o.secs * 10) / 10)}`).join(', ')
          for (const x of show.slice(0, v.key === 'rw' || v.key.startsWith('suite') ? 400 : 120)) p(`| ${x.task} | ${x.kind}${x.solid ? ' (solid)' : ''} | ${x.cand} | ${x.base} | ${x.atLimit ? 'yes' : ''} | ${os(x.samples.cand)} / ${os(x.samples.base)} |`)
          if (show.length > 120 && v.key !== 'rw') p(`| ... ${show.length - 120} more in report.json | | | | | |`)
        }
        p()
        J[v.key] = {candidate: hc, base: hb, mean, differing: D.length, outsideBand: outside.length, tasks: cmp.map(x => ({task: x.task, kind: x.kind, solid: x.solid, atLimit: x.atLimit, inBand: x.inBand, cand: x.cand, base: x.base}))}
      } else J[v.key] = {candidate: hc}
      if (v.key === 'g332' && bs.length) g332(r, cand, base, p)
      if (v.key.startsWith('suite')) { const f = [...c].filter(([, o]) => !o.solved).map(([t]) => t); p(`- Failed on the candidate: ${f.length ? f.join(', ') : 'none'}.\n`) }
      if (v.key === 'lean') { const f = [...c].filter(([, o]) => !o.solved).map(([t]) => t); p(`- ${hc.checked} of ${hc.sampled} checked by Lean, at most ${fmt(hc.max_s!)} s a file${f.length ? `; not checked: ${f.join(', ')}` : ''}.\n`) }
    }
  }
  const sc = size(cand.path), sb = size(base.path)
  p('## Size')
  p()
  p(`core/ and kernel/ (.ts, tests excluded): ${fmt(sc.bytes)} bytes and ${fmt(sc.lines)} lines, against ${fmt(sb.bytes)} and ${fmt(sb.lines)} (${sign(sc.bytes - sb.bytes)} bytes, ${sign(sc.lines - sb.lines)} lines).`)
  p()
  const wall = Math.round((Date.now() - t0) / 1000), secs = jobSeconds(outDir)
  const metas = results.flatMap(r => r.metas), batches = metas.filter(m => m.batch).length
  p('## Wall time')
  p()
  p(`- Wall: ${fmt(wall)} s.`)
  p(`- Job time: ${fmt(secs)} s summed over this bar's ${fmt(batches)} batch(es)${together ? '' : ' (the shared baseline\'s runs apart)'}, on instabox, which bills its boxes by the second; the bar has no bill to read.`)
  p()
  J.size = {cand: sc, base: sb}
  J.trees = {cand, base}
  J.started = since.toISOString()
  J.wall_s = wall
  J.jobSeconds = secs
  J.results = results
  J.coverageErrors = coverageErrors
  writeJson(join(outDir, 'report.json'), J)
  writeFileSync(join(outDir, 'REPORT.md'), L.join('\n') + '\n')
  // Keep both reports as evidence, but never certify an unexecuted candidate.
  if (coverageErrors.length) throw new Error(coverageErrors.join('; '))
  return L.join('\n')
}
function onecpu(r: Result, p: (s?: string) => void) {
  const c = testTimes(r.cand!), b = r.base[0] ? testTimes(r.base[0]) : {tests: new Map<string, number[]>(), failed: []}
  const med = (xs: number[]) => { const s = [...xs].sort((x, y) => x - y); return s.length ? (s.length % 2 ? s[(s.length - 1) / 2]! : (s[s.length / 2 - 1]! + s[s.length / 2]!) / 2) : NaN }
  p('## The 5 s-limited tests on 1 vCPU')
  p()
  p(`Failed jobs: candidate ${c.failed.length ? c.failed.join(', ') : 'none'}; base ${b.failed.length ? b.failed.join(', ') : 'none'}. The ten slowest tests by their most on either side:`)
  p()
  p('| test | candidate median ms | candidate most ms | base median ms | base most ms | runs |')
  p('| --- | --- | --- | --- | --- | --- |')
  const keys = [...new Set([...c.tests.keys(), ...b.tests.keys()])].sort((x, y) => Math.max(...(b.tests.get(y) ?? [0]), ...(c.tests.get(y) ?? [0])) - Math.max(...(b.tests.get(x) ?? [0]), ...(c.tests.get(x) ?? [0])))
  for (const k of keys.slice(0, 10)) { const x = c.tests.get(k) ?? [], y = b.tests.get(k) ?? []; p(`| ${k} | ${fmt(med(x))} | ${fmt(Math.max(...x))} | ${fmt(med(y))} | ${fmt(Math.max(...y))} | ${x.length} / ${y.length} |`) }
  p()
}
// (research/dag's step goals, a retired group's: read by `compare` and `report` from its run directories)
function g332(r: Result, cand: Tree, base: Tree, p: (s?: string) => void) {
  const a = goals(r.cand!), b = goals(r.base[0]!)
  let same = 0
  const ratios: number[] = [], diff: string[] = []
  for (const [k, x] of a) { const y = b.get(k); if (!y) continue; if (goalSig(x) === goalSig(y)) same++; else diff.push(k); ratios.push(x.searchMs / Math.max(1, y.searchMs)) }
  ratios.sort((x, y) => x - y)
  const q = (f: number) => ratios.length ? ratios[Math.min(ratios.length - 1, Math.floor(f * ratios.length))]!.toFixed(3) : '-'
  const sum = (m: Map<string, {searchMs: number}>) => [...m.values()].reduce((s, g) => s + g.searchMs, 0)
  p(`- The same search (outcome, leaves, splits, CDCL's decisions, conflicts and nodes) on ${same} of ${a.size} goals (${cand.key} against ${base.key}); search ms summed ${fmt(sum(a))} against ${fmt(sum(b))}; candidate/base per goal p10 ${q(0.1)}, p50 ${q(0.5)}, p90 ${q(0.9)}${diff.length ? `; differ: ${diff.slice(0, 20).join(', ')}` : ''}.`)
  p()
}

// ------------------------------------------------------------------------------------------------------ commands
async function main() {
  if (!SUBS.includes(sub)) throw new Error(`no command ${sub}: ${SUBS.join(', ')}`)
  for (const [k, why] of Object.entries(GONE)) if (flag(k)) throw new Error(`--${k} is gone: ${why}`)
  if (sub === 'read') {
    const [v, ...dirs] = argv.filter((a, i) => !a.startsWith('--') && argv[i - 1] !== '--tree')
    // (--tasks: each task's observation, {task: {answer, solved, wrong?, secs}}, one line a directory)
    for (const d of dirs) { const rows = VIEWS[v!]!.parse(d, opt('tree', MAIN)); console.log(d, JSON.stringify(flag('tasks') ? Object.fromEntries(rows) : VIEWS[v!]!.headline(rows))) }
    return
  }
  if (sub === 'devset') return devsetCmd()
  if (sub === 'report') {
    // the report again from a run directory's report.json (after a fix)
    const dir = argv.find(a => !a.startsWith('--'))!, j = readJson<{results: Result[], trees?: {cand: Tree, base: Tree}, started?: string, wall_s: number}>(join(dir, 'report.json'))
    const shaOf = (side: Side) => j.results.flatMap(r => r.metas).find(m => m.side === side)?.sha ?? ''
    const t = (side: Side): Tree => j.trees?.[side] ?? {path: join(BAR, 'trees', shaOf(side).slice(0, 12)), sha: shaOf(side), key: shaOf(side).slice(0, 12), clean: true, label: shaOf(side).slice(0, 12)}
    const since = new Date(j.started ?? statSync(dir).birthtime)
    console.log(report(j.results, t('cand'), t('base'), dir, Date.now() - j.wall_s * 1000, since))
    return
  }
  if (sub === 'failed') { for (const d of argv.filter(a => !a.startsWith('--'))) console.log(d, lostJobs(d).length, lostJobs(d).slice(0, 3)); return }
  if (sub === 'compare') {
    // Run directories made elsewhere, compared as the bar compares its own: --group chc --cand d --base d1,d2
    // [--cand-reruns d,..] [--base-reruns d,..] [--cand-tree t] [--base-tree t] [--out dir]
    const g = groupOf(opt('group'))
    if (!g) throw new Error(`no group ${opt('group')}: ${[...GROUPS, ...RETIRED].map(x => x.key).join(', ')}`)
    const list = (k: string) => opt(k) ? opt(k).split(',') : []
    const ct = {path: opt('cand-tree', MAIN), sha: '', key: 'cand', clean: true, label: opt('cand')}, bt = {path: opt('base-tree', MAIN), sha: '', key: 'base', clean: true, label: list('base').join(', ')}
    const r: Result = {group: g.key, cand: opt('cand'), base: list('base'), reruns: {cand: list('cand-reruns'), base: list('base-reruns')}, differing: [], metas: []}
    for (const v of views(g)) for (const t of differing(v.parse(r.cand!, ct.path), r.base.map(b => v.parse(b, bt.path)))) if (!r.differing.includes(t)) r.differing.push(t)
    const outDir = opt('out', join(BAR, 'compare', `${g.key}-${Date.now()}`))
    mkdir(outDir)
    console.log(report([r], ct, bt, outDir, Date.now(), new Date()))
    return
  }
  // No tree copy, pilot or pass may launch before admission.
  // Read-only commands above and standalone supercomputer clients do not wait.
  if (quick) barSlot = await acquireBarSlot({log})
  const only = opt('only', '') ? opt('only').split(',') : undefined
  for (const k of only ?? []) {
    if (RETIRED.some(g => g.key === k)) throw new Error(`group ${k} was retired with its Modal runner (gates/README.md): ${GROUPS.map(g => g.key).join(', ')}`)
    if (!GROUPS.some(g => g.key === k)) throw new Error(`no group ${k}: ${GROUPS.map(g => g.key).join(', ')}`)
  }
  const base = treeOf(opt('base', 'main'))
  const t0 = Date.now(), since = new Date()
  if (sub === 'baseline') {
    const gs = GROUPS.filter(g => !g.candOnly && !g.pairAlways && (only ? only.includes(g.key) : true))
    const outDir = join(cacheDir(base), 'pilots')
    const done = new Map<string, Promise<string[]>>()
    for (const g of gs) done.set(g.key, (g.after && done.get(g.after) ? done.get(g.after)! : Promise.resolve([])).then(() => baseline(g, base, nRuns, outDir)))
    const rs = await Promise.allSettled([...done.values()])
    rs.forEach((r, i) => log(`${gs[i]!.key}: ${r.status === 'fulfilled' ? `${r.value.length} run(s)` : String(r.reason)}`))
    log(`baseline ${cacheDir(base)}: ${Math.round((Date.now() - t0) / 1000)} s wall, ${fmt(jobSeconds(cacheDir(base)))} job seconds`)
    return
  }
  const cand = treeOf(opt('cand', resolve(HERE, '..')))
  const name = opt('name', `${cand.key}-vs-${base.key}-${quick ? 'quick' : 'full'}-${since.toISOString().slice(0, 16).replace(/[:T]/g, '')}`)
  const outDir = join(BAR, 'runs', name)
  mkdir(outDir)
  const gs = GROUPS.filter(g => only ? only.includes(g.key) : quick ? g.inQuick : true)
  log(`${cand.label} against ${base.label}: ${gs.map(g => g.key).join(', ')} -> ${outDir}`)
  try {
    const inRun = new Set(gs.map(g => g.key))
    const results = await Promise.all(gs.map(g => groupFlow(g, cand, base, outDir, inRun)))
    console.log(report(results, cand, base, outDir, t0, since))
    log(`report: ${join(outDir, 'REPORT.md')}`)
  } finally {
    if (live.size) await stopAll('the bar is ending')
  }
}

// The dev sets: for each view, from the first run of a base's shared baseline, `devSet`'s stratified sample; the
// pilots are the reference run's two fastest solved tasks.
function devsetCmd() {
  const key = opt('from', '') || readdirSync(join(BAR, 'base')).sort().at(-1)!
  const root = join(BAR, 'base', key), sha = key.split('-')[0]!
  const tree = existsSync(join(BAR, 'trees', sha)) ? join(BAR, 'trees', sha) : MAIN
  // (the sizes from gates/bar-calibrate.ts on every past pair)
  const SIZES: Record<string, number> = {f1: 50, f2: 40, rw: 90}
  const old = devFile()
  // (the retired groups' dev sets are kept as they were: nothing makes them again)
  const d: DevFile = {made: `from runs/bar/base/${key} (${new Date().toISOString().slice(0, 10)})`, views: {...old?.views}, pilot: {...old?.pilot}}
  for (const g of GROUPS) for (const v of views(g)) {
    if (!SIZES[v.key] || !existsSync(join(root, g.key, 'run1'))) continue
    const ref = v.parse(join(root, g.key, 'run1'), tree)
    const dev = devSet(v, ref, SIZES[v.key]!, `${key}/${g.key}/run1`)
    d.views[v.key] = dev
    d.pilot[g.key] = [...ref].filter(([, o]) => o.solved).sort((a, b) => a[1].secs - b[1].secs).slice(0, 2).map(([t]) => t)
    log(`${v.key}: ${dev.size} of ${dev.of} (${Object.keys(dev.strata).length} strata)`)
  }
  for (const s of ['suite']) if (existsSync(join(root, s, 'run1'))) d.pilot[s] = d.pilot['suite-usual'] = [...VIEWS.suite!.parse(join(root, s, 'run1'), tree)].filter(([, o]) => o.solved).sort((a, b) => a[1].secs - b[1].secs).slice(0, 1).map(([t]) => t)
  if (flag('write')) writeJson(DEV_FILE, d)
  else console.log(JSON.stringify({views: Object.fromEntries(Object.entries(d.views).map(([k, v]) => [k, {size: v.size, of: v.of}])), pilot: d.pilot}, null, 1))
}

await main().catch(async (e: unknown) => {
  console.error(e)
  await stopAll('an error')
  process.exit(1)
}).finally(finishAdmission)
